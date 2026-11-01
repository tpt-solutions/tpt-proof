//! Command-line interface for tpt-proof. Only `--version` works so far.

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("--version") | Some("-V") => println!("tpt-proof {}", env!("CARGO_PKG_VERSION")),
        _ => {
            eprintln!("tpt-proof: verification commands are not implemented yet");
            eprintln!("usage: tpt-proof --version");
            std::process::exit(2);
        }
    }
}
