eval-fibonacci :
	cargo run --release -- eval --expression fibonacci.lurk

fibonacci-proof.json : fibonacci.lurk
	cargo run --release -- prove --expression fibonacci.lurk --proof fibonacci-proof.json

fibonacci-proof : fibonacci-proof.json

verify-fibonacci-proof :
	cargo run --release -- verify --proof fibonacci-proof.json

num-list-commitment.json : num-list-function.json
	cargo run --release -- commit --function num-list-function.json --commitment num-list-commitment.json

num-list-input.json : num-list-input.json

num-list-opening.json : num-list-function.json num-list-input.json
	cargo run --release -- open --function num-list-function.json --input num-list-input.lurk --proof num-list-opening.json

num-list-proof : num-list-opening.json

verify-num-list-proof :
	cargo run --release -- verify --proof num-list-opening.json


