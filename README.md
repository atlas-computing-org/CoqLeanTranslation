# Port Libraries Between Coq and Lean

## Motivation

Making high-quality proof libraries takes a ton of work. It would be a shame to duplicate all that work for each ITP language, or to get locked out of using a specific ITP because it doesn't have the right libraries. Cheap library reuse across languages would reduce the burden of language silos.

Translating definitions and proofs from Coq or Lean to the other reduces the silos between the proof libraries in these communities, allowing each community to leverage the others' work and improving collaborations across traditional language boundaries. For instance, software verification in Lean could benefit from Coq's advanced libraries for software, while Coq could benefit from Lean's math libraries. Having equivalent proofs implemented in different ITPs also provides clear benchmarks for comparing research results across ITPs.

LLMs are often good at language translation problems and may provide significant assistance for translation. If LLMs are effective at ITP-to-ITP translation problems, this success may be a stepping stone to LLM assistance on more general formalization problems like semantic parsing.

See the [project plan write-up](https://docs.google.com/document/d/1XqsWGyvpO3O8GcJZCWBJHJkh301qfaH4kcPsZGXf06A) for further motivation along with some project planning. (Note, these plans are an incomplete draft.)

## Experiments

This work involves simple experiments on using ChatGPT-4 as an assistant to iteratively write and translate between Coq and Lean 4 definitions (not proofs). The definitions specify an instruction set architecture (ISA) and example assembly programs and currently comprise ~400 lines of code.

## Experimental Results

### [2024-01-03 Results](https://docs.google.com/document/d/1Dr2FFZMqpPWuhCBRi0nSg_Ji6US_Xm_aGJvQx_5Z2Cc/edit) - Summary:

**Overall: These experiments found that ChatGPT significantly reduced the work to (a) write a toy ISA model and example assembly programs in Coq (~400 SLOC), (b) translate these to Lean, (c) compare the Coq vs. Lean programs for semantic differences, and (d) port a Coq bugfix to Lean as an incremental patch.** ChatGPT also helped write theorems about the behaviors of the example assembly programs, but was not helpful for constructing proofs of these theorems. Takeaway: Similar capabilities could be useful for engineers creating and updating formal specifications, and would be very useful for porting specifications across ITP languages, though practical use relies on scaling up these capabilities. At the demonstrated scale, ChatGPT already seems like a valuable educational aid for novices learning to write formal specifications.

**The most surprising result was that ChatGPT accurately detected minor semantic differences between two implementations, one in Coq and the other in Lean** [4]. The semantic difference was from a bugfix to the Coq code that was made after translating an earlier version of the code into Lean. ChatGPT was also largely successful at patching the Lean code to match the Coq code, making only a couple simple syntactic errors in its patches that were trivial for me to fix [4].

This example of porting a bugfix is a simple case of aligning new translations with existing definitions in the target codebase: the logical update was ported from Coq to Lean as a semantic extension of the existing Lean code instead of making a deep copy. Alignment seems like it is often the hardest part of making translations practically useful.

See [2024-01-03 Results](https://docs.google.com/document/d/1Dr2FFZMqpPWuhCBRi0nSg_Ji6US_Xm_aGJvQx_5Z2Cc/edit) for further observations, nuance, and supporting materials.

## Interested in Extending This Work?

I'd love to have folks build on this work, and I'd love to hear about it if you do. Reach out to daniel@atlascomputing.org if you want to chat about it. Of course, this is all public (MIT license), so do whatever you want.
