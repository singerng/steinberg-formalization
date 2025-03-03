namespace Lean

def Syntax.mapIdent (syn : Syntax) (f : String → String) : Ident :=
  mkIdent <|
    match syn.getId with
    | .str .anonymous s => Name.mkStr .anonymous (f s)
    | i => i

def Syntax.mapIdent₂ (syn₁ syn₂ : Syntax) (f : String → String → String) : Ident :=
  mkIdent <|
    match syn₁.getId, syn₂.getId with
    | .str .anonymous s₁, .str .anonymous s₂ => Name.mkStr .anonymous (f s₁ s₂)
    | i₁, _ => i₁

def Term.mapIdent (term : Term) (f : String → String) : Term :=
  term.raw.mapIdent f

def Term.mapIdent₂ (t₁ t₂ : Term) (f : String → String → String) : Term :=
  Syntax.mapIdent₂ t₁.raw t₂.raw f

def TSyntax.asIdent {kinds : SyntaxNodeKinds} (syn : TSyntax kinds) : TSyntax `ident :=
  syn.raw.mapIdent id

def TSyntax.mapIdent {kinds : SyntaxNodeKinds} (syn : TSyntax kinds) (f : String → String) : Ident :=
  syn.raw.mapIdent f

def TSyntax.mapIdent₂ {kinds : SyntaxNodeKinds} (s₁ s₂ : TSyntax kinds) (f : String → String → String) : Ident :=
  Syntax.mapIdent₂ s₁.raw s₂.raw f
