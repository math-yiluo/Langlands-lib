/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalRestrictionGlue
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc

/-!
# The exceptional inverse image for rational and algebraically closed coefficients

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-existence/_section.md,
clause (4) for the coefficients `E` and `Q̄_ℓ`, which the blueprint proves by
theorem-f-shriek-ell-adic-coefficients (blueprint: theorem-f-shriek-ell-adic-coefficients).

For a finite extension `E` of `ℚ_ℓ` inside `Q̄_ℓ`, and for `Q̄_ℓ` itself, the exceptional
inverse image is the Brown right adjoint of the compactly supported direct image on the
localizing closures, and it preserves `D_ctf`. The proof uses only Brown representability
(`exists_localizingExceptionalAdjoint`), the compactification comparison, and the rational
restriction theorem (`rationalRestrictionGlue`); no integral or finite-coefficient
restriction enters.

## Main statements

* `rationalExceptionalInverseImage_exists`: the lower shriek, its comparison with every
  compactification, and a right adjoint preserving `D_ctf`.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

local notation "S(" T ")" =>
  (constantModelBoundedConstructible Λ T ⊓ fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K)
local notation "L(" T ")" => localizingClosureProEtale Λ T

/-- For coefficients `E` (a finite extension of `ℚ_ℓ` in `Q̄_ℓ`) or `Q̄_ℓ`, the compactly
supported direct image of the chosen compactification preserves the localizing closures,
agrees with that of every compactification, and has a right adjoint preserving `D_ctf`.

Source: blueprint main-20261015, theorem-exceptional-inverse-image, clauses (2)--(4) for `E` and
`Q̄_ℓ` (blueprint: theorem-f-shriek-ell-adic-coefficients).

Proof:
1. The coefficient is localizing-admissible. Brown representability
   (`exists_localizingExceptionalAdjoint`) gives the preservation of the localizing closures,
   the lower shriek on them and its right adjoint `G`.
2. The compactification cocycle identifies the lower shriek of the chosen compactification
   with the restriction of that of any other compactification.
3. theorem-f-shriek-ell-adic-coefficients (`rationalRestrictionGlue`), applied to the same
adjunction, shows
   that `G` preserves bounded constructible objects. For these coefficients `D_ctf` equals
   `D_bc` (det-def-localizing-closure-ctf-equals-bc), so `G` preserves `D_ctf`.
-/
theorem rationalExceptionalInverseImage_exists
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ℓ k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))) :
    ∃ h : ∀ K, L(X.left) K → L(Y.left)
        ((rightDerivedLowerShriekOfCompactification Λ (compactificationOverField f)).obj K),
      (∀ c : Compactification f.left, Nonempty
        ((localizingLowerShriek Λ (compactificationOverField f) h) ⋙ L(Y.left).ι ≅
          L(X.left).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c)) ∧
      ∃ G : L(Y.left).FullSubcategory ⥤ L(X.left).FullSubcategory,
        Nonempty (localizingLowerShriek Λ (compactificationOverField f) h ⊣ G) ∧
        ∀ N : L(Y.left).FullSubcategory, S(Y.left) N.obj → S(X.left) (G.obj N).obj := by
  classical
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  let : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  let : f.left.IsOver (Spec (.of k)) := ⟨f.w⟩
  let : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X.hom›
  let : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType Y.hom›
  let : QuasiCompact (X.left ↘ Spec (.of k)) := ‹QuasiCompact X.hom›
  let : QuasiCompact (Y.left ↘ Spec (.of k)) := ‹QuasiCompact Y.hom›
  let : IsSeparated (X.left ↘ Spec (.of k)) := ‹IsSeparated X.hom›
  let : IsSeparated (Y.left ↘ Spec (.of k)) := ‹IsSeparated Y.hom›
  have : IsSeparated (f.left ≫ Y.hom) := f.w.symm ▸ ‹IsSeparated X.hom›
  let : IsSeparated f.left := IsSeparated.of_comp f.left Y.hom
  have : LocallyOfFiniteType (f.left ≫ Y.hom) :=
    f.w.symm ▸ ‹LocallyOfFiniteType X.hom›
  let : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  let : QuasiCompact f.left := by infer_instance
  let c : Compactification.BoundaryCompactification f.left :=
    ⟨⟨compactificationOverField f, Compactification.quasiCompact_openImmersion _ inferInstance⟩⟩
  have hadm : IsLocalizingAdmissibleCoefficient ℓ Λ := by
    rcases hΛ with hE | hQ
    · exact Or.inr (Or.inr (Or.inr (Or.inl hE)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hQ))))
  obtain ⟨h, hX, hY, _, ⟨sX⟩, ⟨sY⟩, _, G, s, _, _, adj, _⟩ :=
    exists_localizingExceptionalAdjoint (hcd := hcd) Λ ℓ k f.left c hadm
  refine ⟨h, ?_, G, ⟨adj⟩, ?_⟩
  · intro d
    let d' : Compactification.BoundaryCompactification f.left :=
      ⟨⟨d, d.quasiCompact_openImmersion inferInstance⟩⟩
    obtain ⟨φ, _⟩ := compactification_coherence_cocycle Λ ℓ hadm k f.left
    exact ⟨(L(Y.left).liftCompιIso _ _) ≪≫ φ c d'⟩
  · obtain ⟨E, hE⟩ : ∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
            (Profinite.padicSubfieldCondensedRing ℓ E.1))) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) := by
      rcases hΛ with ⟨E, hE⟩ | hQ
      · exact ⟨E, Or.inl hE⟩
      · exact ⟨⟨⊥, inferInstance⟩, Or.inr hQ⟩
    obtain ⟨_, _, _, hG, _⟩ := (rationalRestrictionGlue.{u, u} (hcd := hcd) Λ ℓ E.1 hE k
      (ringChar k)
      (Fact.out : ringChar k ≠ ℓ) f.left c h G adj).2
    have htor (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T] :
        S(T) = constantModelBoundedConstructible Λ T := by
      apply (localizingClosure_ctf_equals_bc ℓ T Λ ?_).1.2.2.1
      rcases hΛ with ⟨E, hE⟩ | hQ
      · exact Or.inr (Or.inr (Or.inl ⟨E, Or.inr hE⟩))
      · exact Or.inr (Or.inr (Or.inr hQ))
    intro N hN
    exact (congrFun (htor X.left) _).mpr (hG N ((congrFun (htor Y.left) _).mp hN))

end AlgebraicGeometry.ProEtale.CondensedRing
