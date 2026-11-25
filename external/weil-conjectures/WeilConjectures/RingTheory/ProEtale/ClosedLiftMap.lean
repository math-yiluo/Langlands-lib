/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProEtale.ClosedLift

/-! # Functoriality of the ind-etale closed lift

Source: blueprint, smooth purity, `proposition-extension-zero-restriction-closed-subscheme`,
`proposition-extension-zero-restriction-closed-subscheme` (blueprint:
proposition-extension-zero-restriction-closed-subscheme).

The indexing category, diagram, colimit algebra and retained map are the existing
`Algebra.ClosedLift.Index`, `diagram`, `Algebra.ClosedLift` and `toAlgHom`.
This module supplies postcomposition and the resulting map of colimits.
The construction applies to arbitrary input algebras; in particular it applies to
ind-etale algebras over `A ⧸ I`, with their induced `A`-algebra structures.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Algebra.ClosedLift

variable {A C C' : Type u} [CommRing A] [CommRing C] [CommRing C']
  [Algebra A C] [Algebra A C']

/-- The retained map to the input algebra is induced by the factorization maps.
Source: blueprint `proposition-extension-zero-restriction-closed-subscheme`, second paragraph
(blueprint: proposition-extension-zero-restriction-closed-subscheme).
Proof: the defining colimit descent satisfies `colimit.ι_desc` at every index. -/
theorem ι_toAlgHom (X : Index A C) :
    (toAlgHom A C).comp (colimit.ι (diagram A C) X).hom = X.toC :=
  AlgHom.ext (toAlgHom_ι A C X)

/-- Postcomposition preserves compatibility with the input algebra map.
Source: blueprint `proposition-extension-zero-restriction-closed-subscheme`, final sentence
(blueprint: proposition-extension-zero-restriction-closed-subscheme).
Proof: associate the three algebra maps and substitute `f.comp_toC`. -/
theorem postcomp_compatible (φ : C →ₐ[A] C') {X Y : Index A C} (f : X ⟶ Y) :
    (φ.comp Y.toC).comp f.hom = φ.comp X.toC := by
  rw [AlgHom.comp_assoc, f.comp_toC]

/-- Postcomposition on the small indexing categories, leaving all underlying algebra maps
unchanged. Source: blueprint `proposition-extension-zero-restriction-closed-subscheme`, final
sentence (blueprint: proposition-extension-zero-restriction-closed-subscheme). -/
noncomputable def postcomp (φ : C →ₐ[A] C') : Index A C ⥤ Index A C' where
  obj X := ⟨X.n, X.rel, X.etale, φ.comp X.toC⟩
  map f := ⟨f.hom, postcomp_compatible φ f⟩

/-- The map of closed lifts induced by the cocone with components indexed by `(B, φ ∘ q)`.
Source: blueprint `proposition-extension-zero-restriction-closed-subscheme`, final sentence
(blueprint: proposition-extension-zero-restriction-closed-subscheme). -/
noncomputable def map (φ : C →ₐ[A] C') : ClosedLift A C →ₐ[A] ClosedLift A C' :=
  (colimit.desc (diagram A C)
    ((colimit.cocone (diagram A C')).whisker (postcomp φ))).hom

/-- The structure maps characterize the induced map of closed lifts.
Source: blueprint `proposition-extension-zero-restriction-closed-subscheme`, final displayed
equation (blueprint: proposition-extension-zero-restriction-closed-subscheme).
Proof: apply the factorization identity `colimit.ι_desc` to the defining cocone. -/
theorem ι_map (φ : C →ₐ[A] C') (X : Index A C) :
    (map φ).comp (colimit.ι (diagram A C) X).hom =
      (colimit.ι (diagram A C') ((postcomp φ).obj X)).hom := by
  change (colimit.ι (diagram A C) X ≫ colimit.desc (diagram A C)
    ((colimit.cocone (diagram A C')).whisker (postcomp φ))).hom = _
  rw [colimit.ι_desc]
  rfl

/-- The induced map of closed lifts of the identity is the identity. -/
theorem map_id : map (AlgHom.id A C) = AlgHom.id A (ClosedLift A C) := by
  apply CommAlgCat.hom_ext_iff.mp
  apply colimit.hom_ext (F := diagram A C)
  intro X
  apply CommAlgCat.hom_ext
  change (map (AlgHom.id A C)).comp _ = _
  exact ι_map (AlgHom.id A C) X

/-- The induced map of closed lifts of a composite is the composite of the induced maps. -/
theorem map_comp {C'' : Type u} [CommRing C''] [Algebra A C'']
    (φ : C →ₐ[A] C') (ψ : C' →ₐ[A] C'') :
    map (ψ.comp φ) = (map ψ).comp (map φ) := by
  apply CommAlgCat.hom_ext_iff.mp
  apply colimit.hom_ext (F := diagram A C)
  intro X
  apply CommAlgCat.hom_ext
  change (map (ψ.comp φ)).comp _ = ((map ψ).comp (map φ)).comp _
  have h₁ := ι_map (ψ.comp φ) X
  have h₂ := ι_map φ X
  have h₃ := ι_map ψ ((postcomp φ).obj X)
  exact h₁.trans ((congrArg (fun q ↦ (map ψ).comp q) h₂).trans h₃).symm

end Algebra.ClosedLift
