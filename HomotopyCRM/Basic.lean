/-
Copyright (c) 2026 HomotopyCRM Project. All rights reserved.
Clean post-audit Lean 4 formalization slate for:
- Strict 4-tier reflective localization ladder in (infinity, infinity)-categories
- Categorical Reverse Mathematics (CRM) & Fraïssé topological permutation topoi
-/

namespace HomotopyCRM

/-- The four reflective localization tiers inside `Cat^R_(∞,∞) := lim_κ Cat_(∞,n)`
    (Ozornova–Rovelli–Walde 2026, Gepner–Heine 2026). -/
inductive LocalizationTier : Type
  | postnikovL   -- `Cat^L_(∞,∞)`
  | omegaEquiv   -- `Cat^ω_(∞,∞)`
  | coinductive  -- `Cat^coind_(∞,∞)`
  | inductiveR   -- `Cat^R_(∞,∞)`
  deriving DecidableEq, Repr

end HomotopyCRM
