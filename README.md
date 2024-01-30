# Port Libraries Between Coq and Lean

## Motivation

Translating existing theorems and proofs from Coq or Lean to the other reduces the silos between the proof libraries in these communities, allowing each community to leverage the others' work and creating the opportunity to collaborate across traditional language boundaries. For instance, software verification in Lean could benefit from Coq's advanced libraries for software, while Coq could benefit from Lean's math libraries. Having equivalent proofs implemented in different ITPs also provides clear benchmarks for comparing research results across ITPs. LLMs are often good at language translation problems and may provide significant assistance for translation. If LLMs are successful, this could be an early stepping stone to using LLM assistance on more general formalization problems like semantic parsing.

See the [project plan write-up](https://docs.google.com/document/d/1_VU6O4HxVIlNRRcjY8KoNGtjrurlMtDQbN_gdJDsIq0) for further motivation along with some project planning. (Note, these plans are an incomplete draft.)

## Experimental Results

### [2024-01-03 Results](https://docs.google.com/document/d/1Dr2FFZMqpPWuhCBRi0nSg_Ji6US_Xm_aGJvQx_5Z2Cc/edit) - Summary:

**Overall:** The experiments used ChatGPT as an assistant to iteratively write and translate Coq and Lean definitions (not proofs). **These experiments found that ChatGPT significantly reduced the work to (a) write a toy ISA model and example assembly programs in Coq (~400 SLOC), (b) translate these to Lean, (c) compare the Coq vs. Lean programs for semantic differences, and (d) port a Coq bugfix to Lean as an incremental patch.** ChatGPT also helped write theorems about the behaviors of the example assembly programs, but was not helpful for constructing proofs of these theorems. Takeaway: Similar capabilities could be useful for engineers creating and updating formal specifications, and would be very useful for porting specifications across ITP languages, though practical use relies on scaling up these capabilities. At the demonstrated scale, ChatGPT already seems like a valuable educational aid for novices learning to write formal specifications.

**The most surprising result was that ChatGPT accurately detected minor semantic differences between two implementations, one in Coq and the other in Lean** [4]. The semantic difference was from a bugfix to the Coq code that was made after translating an earlier version of the code into Lean. ChatGPT was also largely successful at patching the Lean code to match the Coq code, making only a couple simple syntactic errors in its patches that were trivial for me to fix [4].

This example of porting a bugfix is a simple case of aligning new translations with existing definitions in the target codebase: the logical update was ported from Coq to Lean as a semantic extension of the existing Lean code instead of making a deep copy. Alignment seems like it is often the hardest part of making translations practically useful.

See [2024-01-03 Results](https://docs.google.com/document/d/1Dr2FFZMqpPWuhCBRi0nSg_Ji6US_Xm_aGJvQx_5Z2Cc/edit) for further observations, nuance, and supporting materials.

## Interested in Extending This Work?

I'd love to have folks build on this work, and I'd love to hear about it if you do. Reach out to daniel@atlascomputing.org if you want to chat about it. Of course, this is all public (MIT license), so do whatever you want.
