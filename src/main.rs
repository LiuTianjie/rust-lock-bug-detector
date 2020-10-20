#![feature(rustc_private)]
#![feature(box_patterns)]

extern crate rustc_driver;
extern crate rustc_interface;

mod config;
mod conflict_lock_checker;
mod double_lock_checker;

use config::*;
use conflict_lock_checker::ConflictLockChecker;
use double_lock_checker::DoubleLockChecker;
use rustc_driver::Compilation;
use rustc_interface::{interface, Queries};

struct DetectorCallbacks;

impl rustc_driver::Callbacks for DetectorCallbacks {
    // 在分析完毕后执行回调函数，此时已经有了MIR表示、tcx等
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        // 如果编译出错则终止进程
        compiler.session().abort_if_errors();
        // 对每一个tcx进行操作
        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            // 加载锁检测器的相关配置
            let lock_config = LockDetectorConfig::from_env().unwrap();
            // 对不同的锁检测器执行不同的操作
            match lock_config.lock_detector_type {
                // 匹配到DoubleLockDetector
                LockDetectorType::DoubleLockDetector => match lock_config.crate_name_lists {
                    // 继续匹配crate类型（黑/白）
                    CrateNameLists::Black(crate_name_black_lists) => {
                        // 实例化两段锁检测器
                        let mut double_lock_checker =
                            DoubleLockChecker::new(false, crate_name_black_lists);
                        // 执行检测操作
                        double_lock_checker.check(tcx);
                    }
                    //同上
                    CrateNameLists::White(crate_name_white_lists) => {
                        let mut double_lock_checker =
                            DoubleLockChecker::new(true, crate_name_white_lists);
                        double_lock_checker.check(tcx);
                    }
                },
                // 匹配到ConflictLockDetector
                LockDetectorType::ConflictLockDetector => match lock_config.crate_name_lists {
                    CrateNameLists::Black(crate_name_black_lists) => {
                        let mut conflict_lock_checker =
                            ConflictLockChecker::new(false, crate_name_black_lists);
                        conflict_lock_checker.check(tcx);
                    }
                    CrateNameLists::White(crate_name_white_lists) => {
                        let mut conflict_lock_checker =
                            ConflictLockChecker::new(true, crate_name_white_lists);
                        conflict_lock_checker.check(tcx);
                    }
                },
            }
        });
        // 继续编译
        Compilation::Continue
    }
}

fn compile_time_sysroot() -> Option<String> {
    // 在编译时检查环境变量
    if option_env!("RUST_STAGE").is_some() {
        return None;
    }
    let home = option_env!("RUSTUP_HOME").or(option_env!("MULTIRUST_HOME"));
    let toolchain = option_env!("RUSTUP_TOOLCHAIN").or(option_env!("MULTIRUST_TOOLCHAIN"));
    Some(match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
        _ => option_env!("RUST_SYSROOT")
            .expect("To build rust-lock-bug-detector without rustup, set the `RUST_SYSROOT` env var at build time")
            .to_owned(),
    })
}

fn main() {
    // 收集编译参数
    let mut rustc_args = vec![];
    for arg in std::env::args() {
        rustc_args.push(arg);
    }

    if let Some(sysroot) = compile_time_sysroot() {
        let sysroot_flag = "--sysroot";
        // 当"sysroot_flag"与rustc_args中的参数全部不相同时，将其加入rustc_flag
        if !rustc_args.iter().any(|e| e == sysroot_flag) {
            // We need to overwrite the default that librustc would compute.
            rustc_args.push(sysroot_flag.to_owned());
            rustc_args.push(sysroot);
        }
    }

    let result = rustc_driver::catch_fatal_errors(move || {
        // 调用编译进程，传入编译参数和回调函数
        rustc_driver::run_compiler(&rustc_args, &mut DetectorCallbacks, None, None)
    })
    .and_then(|result| result);

    std::process::exit(result.is_err() as i32);
}
