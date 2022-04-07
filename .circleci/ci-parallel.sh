#!/usr/bin/env bash

grep -A2 -r '\#\[test\]' src/proof/nova.rs | grep -oP '(?<=fn).*?(?=\()' > nova-tests.txt
grep 'recursion' nova-tests.txt > nova-recursion-tests.txt
grep -v 'recursion' nova-tests.txt > nova-tests-tmp.txt
split -l 17 nova-tests-tmp.txt nova-tests --additional-suffix=.txt
rm nova-tests.txt nova-tests-tmp.txt
cat nova-recursion-tests.txt
cat nova-testsaa.txt
cat nova-testsab.txt
cat nova-testsac.txt
circleci tests glob "*.txt" | circleci tests split > tests-to-run
cat tests-to-run

while read name;
do
    cargo test "$name" --release -- --ignored
done <$(cat tests-to-run)

rm *.txt

echo "Tests complete"
