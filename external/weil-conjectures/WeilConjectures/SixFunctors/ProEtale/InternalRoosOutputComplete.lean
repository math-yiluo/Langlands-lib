/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.SixFunctors.ProEtale.InternalPrincipalConeHomReflection
import WeilConjectures.SixFunctors.ProEtale.InternalQuotientPrincipalConeComparison

/-! # Completeness of the internal quotient Roos completion

Source: Stacks 099B and 0A0E; blueprint derived-completion reflector.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.AdicCompletion

/-- The actual Roos completion of a K-flat representative is itself complete.
Source: Stacks 099B and 0A0E; blueprint proposition-proper-base-change-complete-integral
(auxiliary; not a blueprint node).

Proof: choose the coefficient uniformizer endomorphism d. The normalized comparison
identifies the quotient Roos output of P with its principal cone completion. Resolve
that output by a K-flat R, so Q(R) is isomorphic to the principal completion of P.
The Hom reflection property extends this isomorphism uniquely across the principal
completion unit v of R. Composing the extension with the inverse isomorphism gives
a left inverse s of v. Injectivity of precomposition with v, now into the principal
completion of R itself, shows s v = 1 as well. Thus v is invertible. The normalized
comparison for R identifies v followed by an isomorphism with its actual quotient
augmentation. This augmentation is invertible, and R with its resolution is exactly
the witness required by IsDerivedComplete for the original quotient Roos output.
No output K-flatness or completeness of a triangle's arbitrary first vertex is used. -/
theorem isDerivedComplete_roos
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (P : CochainComplex (Modules l E X) ℤ)
    (hP : (HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat P) :
    IsDerivedComplete l E X (DerivedCategory.Q.obj (roos l E X P)) := by
  obtain ⟨d, hd, _⟩ := DerivedNakayama.derived_nakayama_resolution l E
  obtain ⟨cP, _⟩ := internal_quotient_principal_cone_comparison l E X d hd P hP
  obtain ⟨R, q, hq, _, hR⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (roos l E X P)
  have := hq
  let eR := asIso (DerivedCategory.Q.map q)
  let e := eR ≪≫ cP.symm
  obtain ⟨cR, hcR⟩ := internal_quotient_principal_cone_comparison l E X d hd R hR
  let v := DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit
    (End.of (DerivedNakayama.scalarOnComplex l E X d R)))
  obtain ⟨r, hr⟩ :=
    (internal_principal_cone_hom_reflection l E X d hd R P).surjective e.hom
  change v ≫ r = e.hom at hr
  let s := r ≫ e.inv
  have hs : v ≫ s = 𝟙 _ := by
    dsimp only [s]
    rw [← Category.assoc, hr, Iso.hom_inv_id]
  have hright : s ≫ v = 𝟙 _ := by
    apply (internal_principal_cone_hom_reflection l E X d hd R R).injective
    change v ≫ (s ≫ v) = v ≫ 𝟙 _
    rw [← Category.assoc, hs, Category.id_comp, Category.comp_id]
  have : IsIso v := ⟨⟨s, hs, hright⟩⟩
  have : IsIso (DerivedCategory.Q.map (augmentation l E X R)) := by
    rw [← hcR]
    exact inferInstanceAs (IsIso (v ≫ cR.hom))
  exact ⟨R, hR, ⟨eR⟩, inferInstance⟩

end AlgebraicGeometry.ProEtale.AdicCompletion
