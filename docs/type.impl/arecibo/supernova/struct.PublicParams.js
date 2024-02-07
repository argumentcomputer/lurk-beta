(function() {var type_impls = {
"lurk":[["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-PublicParams%3CE1%3E\" class=\"impl\"><a href=\"#impl-PublicParams%3CE1%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;E1&gt; PublicParams&lt;E1&gt;<span class=\"where fmt-newline\">where\n    E1: CurveCycleEquipped,</span></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.setup\" class=\"method\"><h4 class=\"code-header\">pub fn <a class=\"fn\">setup</a>&lt;NC&gt;(\n    non_uniform_circuit: <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.75.0/std/primitive.reference.html\">&amp;NC</a>,\n    ck_hint1: &amp;(dyn <a class=\"trait\" href=\"https://doc.rust-lang.org/1.75.0/core/ops/function/trait.Fn.html\" title=\"trait core::ops::function::Fn\">Fn</a>(&amp;R1CSShape&lt;E1&gt;) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.75.0/std/primitive.usize.html\">usize</a> + 'static),\n    ck_hint2: &amp;(dyn <a class=\"trait\" href=\"https://doc.rust-lang.org/1.75.0/core/ops/function/trait.Fn.html\" title=\"trait core::ops::function::Fn\">Fn</a>(&amp;R1CSShape&lt;&lt;E1 as CurveCycleEquipped&gt;::Secondary&gt;) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.75.0/std/primitive.usize.html\">usize</a> + 'static)\n) -&gt; PublicParams&lt;E1&gt;<span class=\"where fmt-newline\">where\n    NC: NonUniformCircuit&lt;E1&gt;,</span></h4></section></summary><div class=\"docblock\"><p>Construct a new [<code>PublicParams</code>]</p>\n<h5 id=\"note\"><a href=\"#note\">Note</a></h5>\n<p>Public parameters set up a number of bases for the homomorphic commitment scheme of Nova.</p>\n<p>Some final compressing SNARKs, like variants of Spartan, use computation commitments that require\nlarger sizes for these parameters. These SNARKs provide a hint for these values by\nimplementing <code>RelaxedR1CSSNARKTrait::commitment_key_floor()</code>, which can be passed to this function.</p>\n<p>If you’re not using such a SNARK, pass <code>&amp;(|_| 0)</code> instead.</p>\n<h5 id=\"arguments\"><a href=\"#arguments\">Arguments</a></h5>\n<ul>\n<li><code>non_uniform_circuit</code>: The non-uniform circuit of type <code>NC</code>.</li>\n<li><code>ck_hint1</code>: A <code>CommitmentKeyHint</code> for <code>E1</code>, which is a function that provides a hint\nfor the number of generators required in the commitment scheme for the primary circuit.</li>\n<li><code>ck_hint2</code>: A <code>CommitmentKeyHint</code> for <code>E2</code>, similar to <code>ck_hint1</code>, but for the secondary circuit.</li>\n</ul>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.into_parts\" class=\"method\"><h4 class=\"code-header\">pub fn <a class=\"fn\">into_parts</a>(self) -&gt; (<a class=\"struct\" href=\"https://doc.rust-lang.org/1.75.0/alloc/vec/struct.Vec.html\" title=\"struct alloc::vec::Vec\">Vec</a>&lt;R1CSWithArity&lt;E1&gt;&gt;, AuxParams&lt;E1&gt;)</h4></section></summary><div class=\"docblock\"><p>Breaks down an instance of [<code>PublicParams</code>] into the circuit params and auxiliary params.</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.from_parts\" class=\"method\"><h4 class=\"code-header\">pub fn <a class=\"fn\">from_parts</a>(\n    circuit_shapes: <a class=\"struct\" href=\"https://doc.rust-lang.org/1.75.0/alloc/vec/struct.Vec.html\" title=\"struct alloc::vec::Vec\">Vec</a>&lt;R1CSWithArity&lt;E1&gt;&gt;,\n    aux_params: AuxParams&lt;E1&gt;\n) -&gt; PublicParams&lt;E1&gt;</h4></section></summary><div class=\"docblock\"><p>Create a [<code>PublicParams</code>] from a vector of raw [<code>R1CSWithArity</code>] and auxiliary params.</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.from_parts_unchecked\" class=\"method\"><h4 class=\"code-header\">pub fn <a class=\"fn\">from_parts_unchecked</a>(\n    circuit_shapes: <a class=\"struct\" href=\"https://doc.rust-lang.org/1.75.0/alloc/vec/struct.Vec.html\" title=\"struct alloc::vec::Vec\">Vec</a>&lt;R1CSWithArity&lt;E1&gt;&gt;,\n    aux_params: AuxParams&lt;E1&gt;\n) -&gt; PublicParams&lt;E1&gt;</h4></section></summary><div class=\"docblock\"><p>Create a [<code>PublicParams</code>] from a vector of raw [<code>R1CSWithArity</code>] and auxiliary params.\nWe don’t check that the <code>aux_params.digest</code> is a valid digest for the created params.</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.digest\" class=\"method\"><h4 class=\"code-header\">pub fn <a class=\"fn\">digest</a>(&amp;self) -&gt; &lt;E1 as Engine&gt;::Scalar</h4></section></summary><div class=\"docblock\"><p>Return the [<code>PublicParams</code>]’ digest.</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.circuit_param_digests\" class=\"method\"><h4 class=\"code-header\">pub fn <a class=\"fn\">circuit_param_digests</a>(&amp;self) -&gt; CircuitDigests&lt;E1&gt;</h4></section></summary><div class=\"docblock\"><p>All of the primary circuit digests of this [<code>PublicParams</code>]</p>\n</div></details></div></details>",0,"lurk::proof::supernova::SuperNovaPublicParams"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Serialize-for-PublicParams%3CE1%3E\" class=\"impl\"><a href=\"#impl-Serialize-for-PublicParams%3CE1%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;E1&gt; <a class=\"trait\" href=\"https://docs.rs/serde/1.0.196/serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a> for PublicParams&lt;E1&gt;<span class=\"where fmt-newline\">where\n    E1: CurveCycleEquipped,</span></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.serialize\" class=\"method trait-impl\"><a href=\"#method.serialize\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://docs.rs/serde/1.0.196/serde/ser/trait.Serialize.html#tymethod.serialize\" class=\"fn\">serialize</a>&lt;__S&gt;(\n    &amp;self,\n    __serializer: __S\n) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/1.75.0/core/result/enum.Result.html\" title=\"enum core::result::Result\">Result</a>&lt;&lt;__S as <a class=\"trait\" href=\"https://docs.rs/serde/1.0.196/serde/ser/trait.Serializer.html\" title=\"trait serde::ser::Serializer\">Serializer</a>&gt;::<a class=\"associatedtype\" href=\"https://docs.rs/serde/1.0.196/serde/ser/trait.Serializer.html#associatedtype.Ok\" title=\"type serde::ser::Serializer::Ok\">Ok</a>, &lt;__S as <a class=\"trait\" href=\"https://docs.rs/serde/1.0.196/serde/ser/trait.Serializer.html\" title=\"trait serde::ser::Serializer\">Serializer</a>&gt;::<a class=\"associatedtype\" href=\"https://docs.rs/serde/1.0.196/serde/ser/trait.Serializer.html#associatedtype.Error\" title=\"type serde::ser::Serializer::Error\">Error</a>&gt;<span class=\"where fmt-newline\">where\n    __S: <a class=\"trait\" href=\"https://docs.rs/serde/1.0.196/serde/ser/trait.Serializer.html\" title=\"trait serde::ser::Serializer\">Serializer</a>,</span></h4></section></summary><div class='docblock'>Serialize this value into the given Serde serializer. <a href=\"https://docs.rs/serde/1.0.196/serde/ser/trait.Serialize.html#tymethod.serialize\">Read more</a></div></details></div></details>","Serialize","lurk::proof::supernova::SuperNovaPublicParams"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Debug-for-PublicParams%3CE1%3E\" class=\"impl\"><a href=\"#impl-Debug-for-PublicParams%3CE1%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;E1&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.75.0/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a> for PublicParams&lt;E1&gt;<span class=\"where fmt-newline\">where\n    E1: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.75.0/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a> + CurveCycleEquipped,\n    &lt;E1 as Engine&gt;::Scalar: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.75.0/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a>,</span></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.fmt\" class=\"method trait-impl\"><a href=\"#method.fmt\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/1.75.0/core/fmt/trait.Debug.html#tymethod.fmt\" class=\"fn\">fmt</a>(&amp;self, f: &amp;mut <a class=\"struct\" href=\"https://doc.rust-lang.org/1.75.0/core/fmt/struct.Formatter.html\" title=\"struct core::fmt::Formatter\">Formatter</a>&lt;'_&gt;) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/1.75.0/core/result/enum.Result.html\" title=\"enum core::result::Result\">Result</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/1.75.0/std/primitive.unit.html\">()</a>, <a class=\"struct\" href=\"https://doc.rust-lang.org/1.75.0/core/fmt/struct.Error.html\" title=\"struct core::fmt::Error\">Error</a>&gt;</h4></section></summary><div class='docblock'>Formats the value using the given formatter. <a href=\"https://doc.rust-lang.org/1.75.0/core/fmt/trait.Debug.html#tymethod.fmt\">Read more</a></div></details></div></details>","Debug","lurk::proof::supernova::SuperNovaPublicParams"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Index%3Cusize%3E-for-PublicParams%3CE1%3E\" class=\"impl\"><a href=\"#impl-Index%3Cusize%3E-for-PublicParams%3CE1%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;E1&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.75.0/core/ops/index/trait.Index.html\" title=\"trait core::ops::index::Index\">Index</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/1.75.0/std/primitive.usize.html\">usize</a>&gt; for PublicParams&lt;E1&gt;<span class=\"where fmt-newline\">where\n    E1: CurveCycleEquipped,</span></h3></section></summary><div class=\"impl-items\"><details class=\"toggle\" open><summary><section id=\"associatedtype.Output\" class=\"associatedtype trait-impl\"><a href=\"#associatedtype.Output\" class=\"anchor\">§</a><h4 class=\"code-header\">type <a href=\"https://doc.rust-lang.org/1.75.0/core/ops/index/trait.Index.html#associatedtype.Output\" class=\"associatedtype\">Output</a> = R1CSWithArity&lt;E1&gt;</h4></section></summary><div class='docblock'>The returned type after indexing.</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.index\" class=\"method trait-impl\"><a href=\"#method.index\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/1.75.0/core/ops/index/trait.Index.html#tymethod.index\" class=\"fn\">index</a>(&amp;self, index: <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.75.0/std/primitive.usize.html\">usize</a>) -&gt; &amp;&lt;PublicParams&lt;E1&gt; as <a class=\"trait\" href=\"https://doc.rust-lang.org/1.75.0/core/ops/index/trait.Index.html\" title=\"trait core::ops::index::Index\">Index</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/1.75.0/std/primitive.usize.html\">usize</a>&gt;&gt;::<a class=\"associatedtype\" href=\"https://doc.rust-lang.org/1.75.0/core/ops/index/trait.Index.html#associatedtype.Output\" title=\"type core::ops::index::Index::Output\">Output</a></h4></section></summary><div class='docblock'>Performs the indexing (<code>container[index]</code>) operation. <a href=\"https://doc.rust-lang.org/1.75.0/core/ops/index/trait.Index.html#tymethod.index\">Read more</a></div></details></div></details>","Index<usize>","lurk::proof::supernova::SuperNovaPublicParams"]]
};if (window.register_type_impls) {window.register_type_impls(type_impls);} else {window.pending_type_impls = type_impls;}})()