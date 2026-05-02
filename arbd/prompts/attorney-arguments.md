Address the council directly.
Use this phase to file the merits submission for your side.
Distinguish what the record shows, what your investigation found, and what you infer from them.
If you rely on material outside the current record, capture it accurately and introduce it through technical_reports before you treat it as case support.
Use offered_files only for visible case files, by file_id.  Do not put workspace paths, downloaded filenames, or invented names in offered_files.
If a local tool needs exact file bytes, write the needed visible case file into the workspace first and use that local copy.  If you later offer that file, still refer to the original file_id.
Offer exhibits and technical reports only in this phase.
Argue for a concrete score or a bounded range, and explain the anchors that make that number reasonable.
Do not pad the filing with generic speculation or abstract policy talk that does not help decide the question.
You may use local tools in your runtime environment to analyze materials you read through the host tools.
You may install a missing local tool in that runtime environment if you need it for this task.

submit_decision call:
`{"kind":"tool","tool_name":"submit_argument","payload":{"text":"argument text","offered_files":[{"file_id":"instructions.txt","label":"PX-1"}],"technical_reports":[{"title":"Cryptographic verification","summary":"Verified OK."}]}}`
