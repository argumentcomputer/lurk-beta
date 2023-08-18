use ascii_table::AsciiTable;

#[derive(Debug, Clone, Copy)]
struct Prog {
    setup_iterations: usize,
    loop_iterations: usize,
}

fn real_iterations(prog: Prog, n: usize) -> usize {
    prog.setup_iterations + prog.loop_iterations * n
}

fn ceiling(n: usize, m: usize) -> usize {
    n / m + usize::from(n % m != 0)
}

enum Opt<T> {
    Some(T),
    None,
    Empty,
}

impl<T: core::fmt::Display> core::fmt::Display for Opt<T> {
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Opt::None => "-".fmt(fmt),
            Opt::Some(x) => x.fmt(fmt),
            Opt::Empty => "".fmt(fmt),
        }
    }
}

fn total_iterations(real_iterations: usize, rc: usize) -> Opt<usize> {
    let steps = ceiling(real_iterations, rc);
    let total_iterations = steps * rc;

    if real_iterations < rc {
        Opt::None
    } else {
        Opt::Some(total_iterations)
    }
}
fn rc_total_iterations(prog: Prog, n: usize, rc: usize) -> Opt<usize> {
    let real_iterations = real_iterations(prog, n);
    total_iterations(real_iterations, rc)
}

fn analyze_rcs(prog: Prog, n: usize, rcs: &[usize]) -> Vec<Opt<usize>> {
    let mut analysis = Vec::with_capacity(rcs.len() + 2);
    analysis.push(Opt::Some(n));
    analysis.push(Opt::Empty);
    analysis.extend(rcs.iter().map(|rc| rc_total_iterations(prog, n, *rc)));
    analysis
}

fn analyze_ncs_rcs(prog: Prog, ns: &[usize], rcs: &[usize]) -> Vec<Vec<Opt<usize>>> {
    ns.iter().map(|n| analyze_rcs(prog, *n, rcs)).collect()
}

/// Produces a table of 'real Lurk iterations' proved per loop-iteration/rc combination.
/// If the program has fewer real iterations than rc, no value is produced.
/// Otherwise, the number of total iterations (including padding) is used.
fn main() {
    let args = std::env::args().collect::<Vec<_>>();

    let setup_iterations: usize = args[1].parse().unwrap();
    let loop_iterations: usize = args[2].parse().unwrap();
    let ns = [10, 20, 30, 40, 50, 60, 100, 200];
    let rcs = [100, 200, 300, 400, 500, 600, 700, 800, 900, 1000];

    let prog = Prog {
        setup_iterations,
        loop_iterations,
    };
    let analysis = analyze_ncs_rcs(prog, &ns, &rcs);
    let mut table = AsciiTable::default();

    table.column(0).set_header("n");
    table.column(1).set_header("rc");
    for (i, rc) in rcs.into_iter().enumerate() {
        table.column(i + 2).set_header(rc.to_string());
    }

    println!("\nSetup iterations: {setup_iterations}; Iterations per loop: {loop_iterations}.");
    table.print(analysis);
}
