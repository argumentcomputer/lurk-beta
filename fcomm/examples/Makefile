all: build \
    eval-fibonacci verify-fibonacci-proof verify-fibonacci-proof2 \
    verify-num-list-opening \
	verify-chained-opening verify-chained-opening2 verify-chained-opening2-2

clean:
	rm -f *proof*.json *opening*.json *commitment*.json *claim*.json

build : 
	[ -f ../../target/release/fcomm ] || cargo build --release

eval :
	cargo run --release eval --expression eval-input.lurk --lurk

eval-fibonacci :
	cargo run --release -- eval --expression fibonacci.lurk --lurk

fibonacci-claim.json : fibonacci.lurk
	cargo run --release -- eval --expression fibonacci.lurk --claim fibonacci-claim.json --lurk

fibonacci-proof fibonacci-proof.json : fibonacci.lurk
	cargo run --release -- prove --expression fibonacci.lurk --proof fibonacci-proof.json --lurk

fibonacci-proof2 fibonacci-proof2.json : fibonacci-claim.json
	cargo run --release -- prove --claim fibonacci-claim.json --proof fibonacci-proof2.json

verify-fibonacci-proof : fibonacci-proof.json
	cargo run --release -- verify --proof fibonacci-proof.json

verify-fibonacci-proof2 : fibonacci-proof2.json
	cargo run --release -- verify --proof fibonacci-proof2.json

num-list-commitment.json : num-list-function.json
	cargo run --release -- commit --function num-list-function.json --commitment num-list-commitment.json

num-list-opening num-list-opening.json : num-list-function.json num-list-input.lurk num-list-commitment.json
	cargo run --release -- open --function num-list-function.json --input num-list-input.lurk --proof num-list-opening.json

verify-num-list-opening : num-list-opening.json
	cargo run --release -- verify --proof num-list-opening.json

chained-commitment chained-commitment.json : chained-function.json
	cargo run --release -- commit --function chained-function.json --commitment chained-commitment.json

chained-opening chained-opening.json : chained-function.json chained-input.lurk chained-commitment.json
	cargo run --release open --function chained-function.json --input chained-input.lurk --proof chained-opening.json --chain

verify-chained-opening : chained-opening.json
	cargo run --release -- verify --proof chained-opening.json

chained-opening2 chained-opening2.json : chained-input.lurk chained-opening
	# NOTE: This concrete commitment (39ceb60c198b6b7c9f1ff98dd83026bd282e32307d8bd10a28f19d637c4d8549) can be found
	# in chained-opening.json, but its identity is determistic based on the secret and 'second return value' (cdr)
	# of the function specified in chained-function.json.
	cargo run --release open --commitment 39ceb60c198b6b7c9f1ff98dd83026bd282e32307d8bd10a28f19d637c4d8549 --input chained-input.lurk --proof chained-opening2.json --chain

verify-chained-opening2 : chained-opening2.json
	cargo run --release -- verify --proof chained-opening2.json

chained-opening2-with-request chained-opening2-2.json : chained-opening chained-request.json
	cargo run --release open --request chained-request.json --proof chained-opening2-2.json

verify-chained-opening2-2 : chained-opening2-2.json
	cargo run --release -- verify --proof chained-opening2-2.json
