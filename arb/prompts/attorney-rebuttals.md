Address the council directly.
Use this phase to answer the strongest points in the opposing argument.
Focus on misreadings of the record, weak inferences, gaps in proof, and decisive contrary support.
If a targeted investigation would materially test the opponent's strongest factual premise, run it here.
You may do targeted additional investigation here if it directly helps answer those points.
Use web search, source retrieval, local analysis, or direct technical checks where they bear directly on the opponent's position.
To use native web search through the model, ask for a web search on the exact premise you need to test and name the source type most likely to answer it.
Search for related evidence that bears on the opponent's key premise.  Examples: the full source behind an excerpt they relied on, the rule or clarification behind their interpretation, the original file behind a technical claim, or contemporaneous materials that fix timing or authorship.
If you rely on material outside the current record, capture it accurately and introduce it through technical_reports before you treat it as case support.
Use offered_files only for visible case files, by file_id.  Do not put workspace paths, downloaded filenames, or invented names in offered_files.
If a local tool needs exact file bytes, write the needed visible case file into the workspace first and use that local copy.  If you later offer that file, still refer to the original file_id.
Offer exhibits and technical reports only if they directly answer the opposing argument.
Do not use this phase for a replacement merits presentation or a broad second argument.
Good example: "The defense position depends on A.  A targeted check of B undercuts A."
Bad example: "Their case collapses," without identifying the premise that fails.

submit_decision call:
`{"kind":"tool","tool_name":"submit_rebuttal","payload":{"text":"rebuttal text","offered_files":[{"file_id":"instructions.txt","label":"PX-R1"}],"technical_reports":[{"title":"Targeted rebuttal check","summary":"Result."}]}}`
If you decline to rebut, call submit_decision with kind=pass.
