//! Global config for parallelism.
use anyhow::bail;
use once_cell::sync::Lazy;

pub static CONFIG: Lazy<Config> = Lazy::new(init_config);

fn canned_config_from_env() -> Option<CannedConfig> {
    if let Ok(x) = std::env::var("LURK_CANNED_CONFIG") {
        let canned = CannedConfig::try_from(x.as_str()).ok();

        dbg!(&canned);

        canned
    } else {
        None
    }
}

#[derive(Default, Debug)]
pub enum Flow {
    #[default]
    Sequential,
    Parallel,         // Try to be smart.
    ParallelN(usize), // How many threads to use? (Advisory, might be ignored.)
}

impl Flow {
    pub fn is_sequential(&self) -> bool {
        matches!(self, Self::Sequential)
    }

    pub fn is_parallel(&self) -> bool {
        !self.is_sequential()
    }

    pub fn num_threads(&self) -> usize {
        match self {
            Self::Sequential => 1,
            Self::Parallel => num_cpus::get(),
            Self::ParallelN(threads) => *threads,
        }
    }

    pub fn chunk_size(&self, total_n: usize, min_chunk_size: usize) -> usize {
        if self.is_sequential() {
            total_n
        } else {
            let num_threads = self.num_threads();
            let divides_evenly = total_n % num_threads == 0;

            ((total_n / num_threads) + !divides_evenly as usize).max(min_chunk_size)
        }
    }
}

#[derive(Default, Debug)]
pub struct ParallelConfig {
    pub recursive_steps: Flow,    // Multiple `StepCircuit`s.
    pub synthesis: Flow,          // Synthesis (within one `StepCircuit`)
    pub poseidon_witnesses: Flow, // The poseidon witness part of synthesis.
}

/// Should we use optimized witness-generation when possible?
#[derive(Debug, Default)]
pub struct WitnessGeneration {
    // NOTE: Neptune itself *will* do this transparently at the level of individual hashes, where possible.
    // so this configuration is only required for higher-level decisions.
    pub precompute_neptune: bool,
}

#[derive(Default, Debug)]
pub struct Config {
    pub parallelism: ParallelConfig,
    pub witness_generation: WitnessGeneration,
}

impl Config {
    fn fully_sequential() -> Self {
        Self {
            parallelism: ParallelConfig {
                recursive_steps: Flow::Sequential,
                synthesis: Flow::Sequential,
                poseidon_witnesses: Flow::Sequential,
            },
            witness_generation: WitnessGeneration {
                precompute_neptune: false,
            },
        }
    }

    fn max_parallel_simple() -> Self {
        Self {
            parallelism: ParallelConfig {
                recursive_steps: Flow::Parallel,
                synthesis: Flow::Parallel,
                poseidon_witnesses: Flow::Parallel,
            },
            witness_generation: WitnessGeneration {
                precompute_neptune: true,
            },
        }
    }

    fn parallel_steps_only() -> Self {
        Self {
            parallelism: ParallelConfig {
                recursive_steps: Flow::Parallel,
                synthesis: Flow::Sequential,
                poseidon_witnesses: Flow::Sequential,
            },
            witness_generation: WitnessGeneration {
                precompute_neptune: true,
            },
        }
    }
}

#[derive(Debug)]
enum CannedConfig {
    FullySequential,
    MaxParallelSimple,
    ParallelStepsOnly,
}

impl From<CannedConfig> for Config {
    fn from(canned: CannedConfig) -> Self {
        match canned {
            CannedConfig::FullySequential => Self::fully_sequential(),
            CannedConfig::MaxParallelSimple => Self::max_parallel_simple(),
            CannedConfig::ParallelStepsOnly => Self::parallel_steps_only(),
        }
    }
}

impl TryFrom<&str> for CannedConfig {
    type Error = anyhow::Error;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            "FULLY-SEQUENTIAL" => Ok(Self::FullySequential),
            "MAX-PARALLEL-SIMPLE" => Ok(Self::MaxParallelSimple),
            "PARALLEL-STEPS-ONLY" => Ok(Self::ParallelStepsOnly),
            _ => bail!("Invalid CannedConfig: {s}"),
        }
    }
}

fn init_config() -> Config {
    canned_config_from_env()
        .map(|x| x.into())
        .unwrap_or_else(Config::fully_sequential)
}
