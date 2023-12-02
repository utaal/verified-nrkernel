// Counter Brenchmark for IronSync
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Defines a hash-map that can be replicated.

use std::env;
use std::fs::{remove_file, OpenOptions};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::io::{self, Write};
use env_logger::Logger;

fn obtain_dotnet(ironsync_dir: &Path) -> PathBuf {

    // TODO: add an exist check!

    let dotnet_dir = ironsync_dir.join(".dotnet");

    let dotnet = dotnet_dir.join("dotnet");
    if dotnet.is_file() {
        println!("[dotnet] already installed.");
        return dotnet_dir;
    }

    println!("[dotnet] Installing...");

    let output = Command::new("wget")
        .current_dir(ironsync_dir)
        .args(&["https://dot.net/v1/dotnet-install.sh", "-O", "dotnet-install.sh"])
        .output()
        .expect("failed to downlaod the dotnet install script");

    if !output.status.success() {
        println!("status: {}", output.status);
        io::stdout().write_all(&output.stdout).unwrap();
        io::stderr().write_all(&output.stderr).unwrap();
        panic!("[dotnet] failed to install.");
    }

    let output = Command::new("bash")
        .current_dir(ironsync_dir)
        .args(&["dotnet-install.sh", "--channel", "5.0" , "--install-dir", ".dotnet"])
        .output()
        .expect("failed to downlaod the dotnet install script");

    if !output.status.success() {
        println!("status: {}", output.status);
        io::stdout().write_all(&output.stdout).unwrap();
        io::stderr().write_all(&output.stderr).unwrap();
        panic!("[dotnet] failed to install.");
    }

    println!("[dotnet] Installed.");

    dotnet_dir
}

fn run_linear_dafny() -> PathBuf {

    let cwd = std::env::current_dir().unwrap();
    let benchmarks_dir = cwd.parent().unwrap();
    let nr_dir = benchmarks_dir.parent().unwrap();

    let ironsync_dir = nr_dir.join("ironsync-osdi2023");

    let build_script = ironsync_dir.join("run-dafny-in-docker.sh");
    if !build_script.is_file() {
        let output =  Command::new("git")
            .args(&["submodule", "update", "--init"])
            .output()
            .expect("failed to execute process");

        if !output.status.success() {
            println!("FAILED TO INITIALIZE SUBMODULE!");
            io::stdout().write_all(&output.stdout).unwrap();
            io::stderr().write_all(&output.stderr).unwrap();
            panic!("FAILED TO INITIALIZE SUBMODULE!");
        }

        if !build_script.is_file() {
            panic!("Build script is still missing!");
        }
    }

    let dotnet_path = obtain_dotnet(ironsync_dir.as_path());

    // export PATH="$PATH:$HOME/.dotnet"
    match env::var("PATH") {
        Ok(val) => {
            let new_path = format!("{}:{val}", dotnet_path.display().to_string());
            println!("Updating PATH environment variable to {new_path}");
            env::set_var("PATH", new_path);
        }
        Err(_e) => {
            let new_path = dotnet_path.display().to_string();
            println!("Setting PATH environment variable to {new_path}");
            env::set_var("PATH", new_path);
        }
    }

    let dafny_path = ironsync_dir.join(".dafny");
    let dafny_bin_path = dafny_path.join("bin/dafny");

    println!("[dafny] Checking LinearDafny Version...");
    let output = Command::new("tools/local-dafny.sh")
        .args(&["/version"])
        .envs(env::vars())
        .current_dir(ironsync_dir.clone())
        .output()
        .expect("[dafny] Failed to run command.");

    if !output.status.success() {
        if dafny_path.exists() {
            std::fs::remove_dir_all(dafny_path)
                .expect("[dafny] failed to remove .dafny directory");
        }

        println!("[dafny] Building LinearDafny...");
        let output = Command::new("tools/artifact-setup-dafny.sh")
            .envs(env::vars())
            .current_dir(ironsync_dir.clone())
            .output()
            .expect("[dafny] failed to run `artifact-setup-dafny.sh` command");
        if !output.status.success() {
                println!("status: {}", output.status);
                io::stdout().write_all(&output.stdout).unwrap();
                io::stderr().write_all(&output.stderr).unwrap();
                panic!("[dafny] Dafny Build has failed");
        }

        println!("[dafny] Dafny version ok.");
    }
    println!("[dafny] Dafny version ok.");

    println!("[dafny] Running verifier (nr-status)...");
    let output = Command::new("make")
        .args(["nr-status", "-j"])
        .envs(env::vars())
        .current_dir(ironsync_dir.clone())
        .output().expect("[dafny] failed to run verifier");

    if !output.status.success() {
        println!("status: {}", output.status);
        io::stdout().write_all(&output.stdout).unwrap();
        io::stderr().write_all(&output.stderr).unwrap();
        panic!("[dafny] failed to verify status");
    }

    println!("[dafny] verifier OK (nr-status)...");

    println!("[dafny] building nr binaries");
    let nr_dir = ironsync_dir.join("concurrency/node-replication");

    let filtered_env : std::collections::HashMap<String, String> =
        env::vars().filter(|&(ref k, _)|
            !k.starts_with("CARGO") && k != "RUSTUP_TOOLCHAIN" && k != "RUST_RECURSION_COUNT"
        ).collect();

    let output = Command::new("./compile-bench.sh")
        .env_clear()
        .envs(&filtered_env)
        .current_dir(nr_dir.clone())
        .output()
        .expect("[dafny] failed to exec make command");
    if !output.status.success() {
        println!("status: {}", output.status);
        io::stdout().write_all(&output.stdout).unwrap();
        io::stderr().write_all(&output.stderr).unwrap();
        panic!("[dafny] failed to clean the build");
    }

    println!("[dafny] nr binaries built!");

    nr_dir
}


fn run_bench(nr_dir: PathBuf) {
    println!("[run] running benchmark");
    let output = Command::new("./bench.py")
        .current_dir(nr_dir.clone())
        .output()
        .expect("[run] failed to exec make command");
    if !output.status.success() {
        println!("status: {}", output.status);
        io::stdout().write_all(&output.stdout).unwrap();
        io::stderr().write_all(&output.stderr).unwrap();
        panic!("[run] failed to clean the build");
    }

    println!("[run] benchmark ran successfully");
}

#[cfg(target_os = "linux")]
pub fn disable_dvfs() {
    use std::process;

    let o = process::Command::new("sh")
        .args(&[
            "-s",
            "echo performance | tee /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor",
        ])
        .output()
        .expect("failed to change scaling governor");
    assert!(o.status.success());
}


fn main() {
    let _r = env_logger::try_init();

    disable_dvfs();

    let path = run_linear_dafny();
    run_bench(path)
}
