eval-fibonacci :
	cargo run --release -- eval --expression fibonacci.lurk

fibonacci-proof.json : fibonacci.lurk
	cargo run --release -- prove --expression fibonacci.lurk --proof fibonacci-proof.json

fibonacci-proof : fibonacci-proof.json

verify-fibonacci-proof : fibonacci-proof
	cargo run --release -- verify --proof fibonacci-proof.json


