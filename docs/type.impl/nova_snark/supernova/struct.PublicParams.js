(function() {var type_impls = {
"lurk":[["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-PublicParams%3CE1,+E2,+C1,+C2%3E\" class=\"impl\"><a href=\"#impl-PublicParams%3CE1,+E2,+C1,+C2%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;E1, E2, C1, C2&gt; PublicParams&lt;E1, E2, C1, C2&gt;<span class=\"where fmt-newline\">where\n    E1: Engine&lt;Base = &lt;E2 as Engine&gt;::Scalar&gt;,\n    E2: Engine&lt;Base = &lt;E1 as Engine&gt;::Scalar&gt;,\n    C1: StepCircuit&lt;&lt;E1 as Engine&gt;::Scalar&gt;,\n    C2: StepCircuit&lt;&lt;E2 as Engine&gt;::Scalar&gt;,</span></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.setup\" class=\"method\"><h4 class=\"code-header\">pub fn <a class=\"fn\">setup</a>&lt;NC&gt;(\n    non_uniform_circuit: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;NC</a>,\n    ck_hint1: &amp;(dyn <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/ops/function/trait.Fn.html\" title=\"trait core::ops::function::Fn\">Fn</a>(&amp;R1CSShape&lt;E1&gt;) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.usize.html\">usize</a> + 'static),\n    ck_hint2: &amp;(dyn <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/ops/function/trait.Fn.html\" title=\"trait core::ops::function::Fn\">Fn</a>(&amp;R1CSShape&lt;E2&gt;) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.usize.html\">usize</a> + 'static)\n) -&gt; PublicParams&lt;E1, E2, C1, C2&gt;<span class=\"where fmt-newline\">where\n    NC: NonUniformCircuit&lt;E1, E2, C1, C2&gt;,</span></h4></section></summary><div class=\"docblock\"><p>Construct a new [PublicParams]</p>\n<h5 id=\"note\"><a href=\"#note\">Note</a></h5>\n<p>Public parameters set up a number of bases for the homomorphic commitment scheme of Nova.</p>\n<p>Some final compressing SNARKs, like variants of Spartan, use computation commitments that require\nlarger sizes for these parameters. These SNARKs provide a hint for these values by\nimplementing <code>RelaxedR1CSSNARKTrait::commitment_key_floor()</code>, which can be passed to this function.</p>\n<p>If you’re not using such a SNARK, pass <code>&amp;(|_| 0)</code> instead.</p>\n<h5 id=\"arguments\"><a href=\"#arguments\">Arguments</a></h5>\n<ul>\n<li><code>non_uniform_circuit</code>: The non-uniform circuit of type <code>NC</code>.</li>\n<li><code>ck_hint1</code>: A <code>CommitmentKeyHint</code> for <code>E1</code>, which is a function that provides a hint\nfor the number of generators required in the commitment scheme for the primary circuit.</li>\n<li><code>ck_hint2</code>: A <code>CommitmentKeyHint</code> for <code>E2</code>, similar to <code>ck_hint1</code>, but for the secondary circuit.</li>\n</ul>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.into_parts\" class=\"method\"><h4 class=\"code-header\">pub fn <a class=\"fn\">into_parts</a>(self) -&gt; (<a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/alloc/vec/struct.Vec.html\" title=\"struct alloc::vec::Vec\">Vec</a>&lt;CircuitShape&lt;E1&gt;&gt;, AuxParams&lt;E1, E2&gt;)</h4></section></summary><div class=\"docblock\"><p>Breaks down an instance of [PublicParams] into the circuit params and auxilliary params.</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.from_parts\" class=\"method\"><h4 class=\"code-header\">pub fn <a class=\"fn\">from_parts</a>(\n    circuit_shapes: <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/alloc/vec/struct.Vec.html\" title=\"struct alloc::vec::Vec\">Vec</a>&lt;CircuitShape&lt;E1&gt;&gt;,\n    aux_params: AuxParams&lt;E1, E2&gt;\n) -&gt; PublicParams&lt;E1, E2, C1, C2&gt;</h4></section></summary><div class=\"docblock\"><p>Create a [PublicParams] from a vector of raw [CircuitShape] and auxilliary params.</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.from_parts_unchecked\" class=\"method\"><h4 class=\"code-header\">pub fn <a class=\"fn\">from_parts_unchecked</a>(\n    circuit_shapes: <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/alloc/vec/struct.Vec.html\" title=\"struct alloc::vec::Vec\">Vec</a>&lt;CircuitShape&lt;E1&gt;&gt;,\n    aux_params: AuxParams&lt;E1, E2&gt;\n) -&gt; PublicParams&lt;E1, E2, C1, C2&gt;</h4></section></summary><div class=\"docblock\"><p>Create a [PublicParams] from a vector of raw [CircuitShape] and auxilliary params.\nWe don’t check that the <code>aux_params.digest</code> is a valid digest for the created params.</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.digest\" class=\"method\"><h4 class=\"code-header\">pub fn <a class=\"fn\">digest</a>(&amp;self) -&gt; &lt;E1 as Engine&gt;::Scalar</h4></section></summary><div class=\"docblock\"><p>Return the [PublicParams]’ digest.</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.circuit_param_digests\" class=\"method\"><h4 class=\"code-header\">pub fn <a class=\"fn\">circuit_param_digests</a>(&amp;self) -&gt; CircuitDigests&lt;E1&gt;</h4></section></summary><div class=\"docblock\"><p>All of the primary circuit digests of this [PublicParams]</p>\n</div></details></div></details>",0,"lurk::proof::supernova::SuperNovaPublicParams"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Deserialize%3C'de%3E-for-PublicParams%3CE1,+E2,+C1,+C2%3E\" class=\"impl\"><a href=\"#impl-Deserialize%3C'de%3E-for-PublicParams%3CE1,+E2,+C1,+C2%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'de, E1, E2, C1, C2&gt; <a class=\"trait\" href=\"https://docs.rs/serde/1.0.193/serde/de/trait.Deserialize.html\" title=\"trait serde::de::Deserialize\">Deserialize</a>&lt;'de&gt; for PublicParams&lt;E1, E2, C1, C2&gt;<span class=\"where fmt-newline\">where\n    E1: Engine&lt;Base = &lt;E2 as Engine&gt;::Scalar&gt;,\n    E2: Engine&lt;Base = &lt;E1 as Engine&gt;::Scalar&gt;,\n    C1: StepCircuit&lt;&lt;E1 as Engine&gt;::Scalar&gt;,\n    C2: StepCircuit&lt;&lt;E2 as Engine&gt;::Scalar&gt;,</span></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.deserialize\" class=\"method trait-impl\"><a href=\"#method.deserialize\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://docs.rs/serde/1.0.193/serde/de/trait.Deserialize.html#tymethod.deserialize\" class=\"fn\">deserialize</a>&lt;__D&gt;(\n    __deserializer: __D\n) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/result/enum.Result.html\" title=\"enum core::result::Result\">Result</a>&lt;PublicParams&lt;E1, E2, C1, C2&gt;, &lt;__D as <a class=\"trait\" href=\"https://docs.rs/serde/1.0.193/serde/de/trait.Deserializer.html\" title=\"trait serde::de::Deserializer\">Deserializer</a>&lt;'de&gt;&gt;::<a class=\"associatedtype\" href=\"https://docs.rs/serde/1.0.193/serde/de/trait.Deserializer.html#associatedtype.Error\" title=\"type serde::de::Deserializer::Error\">Error</a>&gt;<span class=\"where fmt-newline\">where\n    __D: <a class=\"trait\" href=\"https://docs.rs/serde/1.0.193/serde/de/trait.Deserializer.html\" title=\"trait serde::de::Deserializer\">Deserializer</a>&lt;'de&gt;,</span></h4></section></summary><div class='docblock'>Deserialize this value from the given Serde deserializer. <a href=\"https://docs.rs/serde/1.0.193/serde/de/trait.Deserialize.html#tymethod.deserialize\">Read more</a></div></details></div></details>","Deserialize<'de>","lurk::proof::supernova::SuperNovaPublicParams"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Serialize-for-PublicParams%3CE1,+E2,+C1,+C2%3E\" class=\"impl\"><a href=\"#impl-Serialize-for-PublicParams%3CE1,+E2,+C1,+C2%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;E1, E2, C1, C2&gt; <a class=\"trait\" href=\"https://docs.rs/serde/1.0.193/serde/ser/trait.Serialize.html\" title=\"trait serde::ser::Serialize\">Serialize</a> for PublicParams&lt;E1, E2, C1, C2&gt;<span class=\"where fmt-newline\">where\n    E1: Engine&lt;Base = &lt;E2 as Engine&gt;::Scalar&gt;,\n    E2: Engine&lt;Base = &lt;E1 as Engine&gt;::Scalar&gt;,\n    C1: StepCircuit&lt;&lt;E1 as Engine&gt;::Scalar&gt;,\n    C2: StepCircuit&lt;&lt;E2 as Engine&gt;::Scalar&gt;,</span></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.serialize\" class=\"method trait-impl\"><a href=\"#method.serialize\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://docs.rs/serde/1.0.193/serde/ser/trait.Serialize.html#tymethod.serialize\" class=\"fn\">serialize</a>&lt;__S&gt;(\n    &amp;self,\n    __serializer: __S\n) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/result/enum.Result.html\" title=\"enum core::result::Result\">Result</a>&lt;&lt;__S as <a class=\"trait\" href=\"https://docs.rs/serde/1.0.193/serde/ser/trait.Serializer.html\" title=\"trait serde::ser::Serializer\">Serializer</a>&gt;::<a class=\"associatedtype\" href=\"https://docs.rs/serde/1.0.193/serde/ser/trait.Serializer.html#associatedtype.Ok\" title=\"type serde::ser::Serializer::Ok\">Ok</a>, &lt;__S as <a class=\"trait\" href=\"https://docs.rs/serde/1.0.193/serde/ser/trait.Serializer.html\" title=\"trait serde::ser::Serializer\">Serializer</a>&gt;::<a class=\"associatedtype\" href=\"https://docs.rs/serde/1.0.193/serde/ser/trait.Serializer.html#associatedtype.Error\" title=\"type serde::ser::Serializer::Error\">Error</a>&gt;<span class=\"where fmt-newline\">where\n    __S: <a class=\"trait\" href=\"https://docs.rs/serde/1.0.193/serde/ser/trait.Serializer.html\" title=\"trait serde::ser::Serializer\">Serializer</a>,</span></h4></section></summary><div class='docblock'>Serialize this value into the given Serde serializer. <a href=\"https://docs.rs/serde/1.0.193/serde/ser/trait.Serialize.html#tymethod.serialize\">Read more</a></div></details></div></details>","Serialize","lurk::proof::supernova::SuperNovaPublicParams"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Clone-for-PublicParams%3CE1,+E2,+C1,+C2%3E\" class=\"impl\"><a href=\"#impl-Clone-for-PublicParams%3CE1,+E2,+C1,+C2%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;E1, E2, C1, C2&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for PublicParams&lt;E1, E2, C1, C2&gt;<span class=\"where fmt-newline\">where\n    E1: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> + Engine&lt;Base = &lt;E2 as Engine&gt;::Scalar&gt;,\n    E2: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> + Engine&lt;Base = &lt;E1 as Engine&gt;::Scalar&gt;,\n    C1: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> + StepCircuit&lt;&lt;E1 as Engine&gt;::Scalar&gt;,\n    C2: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> + StepCircuit&lt;&lt;E2 as Engine&gt;::Scalar&gt;,\n    &lt;E1 as Engine&gt;::Scalar: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a>,</span></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.clone\" class=\"method trait-impl\"><a href=\"#method.clone\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#tymethod.clone\" class=\"fn\">clone</a>(&amp;self) -&gt; PublicParams&lt;E1, E2, C1, C2&gt;</h4></section></summary><div class='docblock'>Returns a copy of the value. <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#tymethod.clone\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.clone_from\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/clone.rs.html#169\">source</a></span><a href=\"#method.clone_from\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#method.clone_from\" class=\"fn\">clone_from</a>(&amp;mut self, source: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;Self</a>)</h4></section></summary><div class='docblock'>Performs copy-assignment from <code>source</code>. <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#method.clone_from\">Read more</a></div></details></div></details>","Clone","lurk::proof::supernova::SuperNovaPublicParams"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Index%3Cusize%3E-for-PublicParams%3CE1,+E2,+C1,+C2%3E\" class=\"impl\"><a href=\"#impl-Index%3Cusize%3E-for-PublicParams%3CE1,+E2,+C1,+C2%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;E1, E2, C1, C2&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/ops/index/trait.Index.html\" title=\"trait core::ops::index::Index\">Index</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.usize.html\">usize</a>&gt; for PublicParams&lt;E1, E2, C1, C2&gt;<span class=\"where fmt-newline\">where\n    E1: Engine&lt;Base = &lt;E2 as Engine&gt;::Scalar&gt;,\n    E2: Engine&lt;Base = &lt;E1 as Engine&gt;::Scalar&gt;,\n    C1: StepCircuit&lt;&lt;E1 as Engine&gt;::Scalar&gt;,\n    C2: StepCircuit&lt;&lt;E2 as Engine&gt;::Scalar&gt;,</span></h3></section></summary><div class=\"impl-items\"><details class=\"toggle\" open><summary><section id=\"associatedtype.Output\" class=\"associatedtype trait-impl\"><a href=\"#associatedtype.Output\" class=\"anchor\">§</a><h4 class=\"code-header\">type <a href=\"https://doc.rust-lang.org/nightly/core/ops/index/trait.Index.html#associatedtype.Output\" class=\"associatedtype\">Output</a> = CircuitShape&lt;E1&gt;</h4></section></summary><div class='docblock'>The returned type after indexing.</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.index\" class=\"method trait-impl\"><a href=\"#method.index\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/ops/index/trait.Index.html#tymethod.index\" class=\"fn\">index</a>(\n    &amp;self,\n    index: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.usize.html\">usize</a>\n) -&gt; &amp;&lt;PublicParams&lt;E1, E2, C1, C2&gt; as <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/ops/index/trait.Index.html\" title=\"trait core::ops::index::Index\">Index</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.usize.html\">usize</a>&gt;&gt;::<a class=\"associatedtype\" href=\"https://doc.rust-lang.org/nightly/core/ops/index/trait.Index.html#associatedtype.Output\" title=\"type core::ops::index::Index::Output\">Output</a></h4></section></summary><div class='docblock'>Performs the indexing (<code>container[index]</code>) operation. <a href=\"https://doc.rust-lang.org/nightly/core/ops/index/trait.Index.html#tymethod.index\">Read more</a></div></details></div></details>","Index<usize>","lurk::proof::supernova::SuperNovaPublicParams"]]
};if (window.register_type_impls) {window.register_type_impls(type_impls);} else {window.pending_type_impls = type_impls;}})()