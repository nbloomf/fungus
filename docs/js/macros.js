window.MathJax = {
  tex: {
    macros: {
      nats: "\\mathbb{N}",
      LambdaIdents: "\\mathbb{I}_\\lambda",
      LambdaConsts: "\\mathbb{C}_\\lambda",
      LambdaTerms: "\\mathsf{Term}_\\lambda",
      lamex: [ "\\texttt{λ} {#1}.{#2}", 2 ],
      letin: [ "\\texttt{@let}\\ {#1}\\ \\texttt{=}\\ {#2}\\ \\texttt{@in}\\ {#3}", 3 ],
      apply: [ "\\texttt{(}{#1}\\ {#2}\\texttt{)}", 2 ],
      height: "\\mathsf{height}",
      size: "\\mathsf{size}",
      freeLambdaVars: "\\mathsf{fv}_{\\lambda}",
      choice: "\\mathsf{choice}",
      LambdaSubstitutions: "\\mathsf{Subst}_\\lambda",
      new: "\\mathsf{new}",
      AlphaEq: "\\equiv_{\\alpha}",
    }
  }
};
