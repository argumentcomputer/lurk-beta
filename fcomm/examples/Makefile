build : ../../target/release/fcomm
	cargo build --release

eval-fibonacci :
	cargo run --release -- eval --expression fibonacci.lurk

fibonacci-claim.json : fibonacci.lurk
	cargo run --release -- eval --expression fibonacci.lurk --claim fibonacci-claim.json --lurk

fibonacci-proof.json : fibonacci.lurk
	cargo run --release -- prove --expression fibonacci.lurk --proof fibonacci-proof.json --lurk

fibonacci-proof2.json : fibonacci-claim.json
	cargo run --release -- prove --claim fibonacci-claim.json --proof fibonacci-proof2.json

fibonacci-proof : fibonacci-proof.json
fibonacci-proof2 : fibonacci-proof2.json

verify-fibonacci-proof :
	cargo run --release -- verify --proof fibonacci-proof.json

num-list-commitment.json : num-list-function.json
	cargo run --release -- commit --function num-list-function.json --commitment num-list-commitment.json

num-list-input.lurk : num-list-input.lurk

num-list-opening.json : num-list-function.json num-list-input.lurk
	cargo run --release -- open --function num-list-function.json --input num-list-input.lurk --proof num-list-opening.json

num-list-proof : num-list-opening.json

verify-num-list-opening :
	cargo run --release -- verify --proof num-list-opening.json

chained-commitment.json : chained-function.json

chained-opening: chained-opening.json

chained-opening.json : chained-function.json chained-input.lurk
	cargo run --release open --function chained-function.json --input chained-input.lurk --proof chained-opening.json --chain

verify-chained-opening :
	cargo run --release -- verify --proof chained-opening.json
