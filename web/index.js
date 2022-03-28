import * as wasm from "lurk-rs";
var output = document.getElementById("output");
function show(text) {
    output.innerText = text;
    console.log(text);
    
}

var runit = document.getElementById("run");
var input = document.getElementById("input");
runit.onclick = function (_e) {
    var source = input.value;
    show("running: " + source);
    show(wasm.run_lurk(source));
};
