all: build eval \
    eval-fibonacci verify-fibonacci-proof verify-fibonacci2-proof \
    verify-num-list-opening \
	verify-chained-opening verify-chained2-opening verify-chained2-from_req-opening

clean:
	rm -f *proof*.json *opening*.json *commitment*.json *claim*.json

build : 
	[ -f ../../target/release/fcomm ] || cargo build --release

%-commitment %-commitment.json : %-function.json
	cargo run --release -- commit --function $*-function.json --commitment $*-commitment.json

%-opening %-opening.json : %-function.json %-input.lurk %-commitment.json
	cargo run --release -- open --function $*-function.json --input $*-input.lurk --proof $*-opening.json

verify-%-proof verify-%-proof.json : %-proof.json
	cargo run --release -- verify --proof $*-proof.json

verify-%-opening verify-%-opening.json : %-opening.json
	cargo run --release -- verify --proof $*-opening.json

eval :
	cargo run --release eval --expression eval-input.lurk --lurk

eval-fibonacci :
	cargo run --release -- eval --expression fibonacci.lurk --lurk

fibonacci-claim.json : fibonacci.lurk
	cargo run --release -- eval --expression fibonacci.lurk --claim fibonacci-claim.json --lurk

fibonacci-proof fibonacci-proof.json : fibonacci.lurk
	cargo run --release -- prove --expression fibonacci.lurk --proof fibonacci-proof.json --lurk

fibonacci2-proof fibonacci2-proof.json : fibonacci-claim.json
	cargo run --release -- prove --claim fibonacci-claim.json --proof fibonacci2-proof.json

chained-opening.json : chained-function.json chained-input.lurk chained-commitment
	cargo run --release open --function chained-function.json --input chained-input.lurk --proof chained-opening.json --chain

chained2-opening chained2-opening.json : chained-input.lurk chained-opening
	# NOTE: This concrete commitment (1d52c2a9a97ed0fd4755e89b4310f1edc7d2c0ef3e250c4e5b51dacefc76caf5) can be found
	# in chained-opening.json, but its identity is determistic based on the secret and 'second return value' (cdr)
	# of the function specified in chained-function.json.
	cargo run --release open --commitment 1d52c2a9a97ed0fd4755e89b4310f1edc7d2c0ef3e250c4e5b51dacefc76caf5 --input chained-input.lurk --proof chained2-opening.json --chain

chained2-from_req-opening chained2-from_req-opening.json : chained2-opening chained-request.json
	cargo run --release open --request chained-request.json --proof chained2-from_req-opening.json
