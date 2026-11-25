/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.DeformationModel
public import WeilConjectures.RingTheory.ExtendedReesAlgebraGraded

/-!
# Properness of the deformation to the normal cone of a nilpotent ideal

For `I` finitely generated and nilpotent, `R[t, I t⁻¹]` is finite over `R[t]`. Hence for `X` proper
over `k` and `I ≤ nilradical X`, `D_I X ⟶ 𝔸¹_k` and its base change to `Spec k'⟦t⟧` are proper.
This applies to the ideal of a rational point of a one-point scheme.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace Ideal

variable {R : Type*} [CommRing R] {I : Ideal R}

/-- The extended Rees algebra of a finitely generated nilpotent ideal is finite over `R[t]`. -/
theorem finite_toExtendedReesAlgebra (hI : I.FG) (hN : IsNilpotent I) :
    I.toExtendedReesAlgebra.Finite := by
  obtain ⟨N, hN⟩ := hN
  refine RingHom.IsIntegral.to_finite ?_ (RingHom.FiniteType.of_comp_finiteType (f := C) ?_)
  · rintro ⟨y, hy⟩
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain rfl | ⟨x, hx, rfl⟩ := hy
      · exact (I.toExtendedReesAlgebra_X ▸ I.toExtendedReesAlgebra.isIntegralElem_map (x := X) :)
      · refine ⟨X ^ N, monic_X_pow N, Subtype.ext ?_⟩
        have : x ^ N = 0 := by simpa [hN] using Ideal.pow_mem_pow hx N
        simp [mul_pow, ← map_pow, this]
    | algebraMap r =>
      exact (I.toExtendedReesAlgebra_C r ▸ I.toExtendedReesAlgebra.isIntegralElem_map (x := C r) :)
    | add x y hx hy ihx ihy => exact RingHom.IsIntegralElem.add _ ihx ihy
    | mul x y hx hy ihx ihy => exact RingHom.IsIntegralElem.mul _ ihx ihy
  · have : I.toExtendedReesAlgebra.comp C = algebraMap R _ := RingHom.ext fun x ↦ by simp
    rw [this, RingHom.finiteType_algebraMap]
    exact finiteType_extendedReesAlgebra hI

end Ideal

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme AffineZariskiSite

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) {I : X.left.IdealSheafData}
  (k' : Type u) [Field k'] [Algebra k k']

/-- For a nilpotent ideal sheaf `I` on a locally noetherian scheme, `D_I X ⟶ 𝔸¹_X` is finite. -/
lemma isFinite_deformationSpaceToPolynomialSpec [IsLocallyNoetherian X.left]
    (hI : I ≤ X.left.nilradical) : IsFinite I.deformationSpaceToPolynomialSpec := by
  refine relativeGluingMap_of_forall (P := @IsFinite) _ _ _
    I.toPolynomialPresheaf_comp_polynomialToRees fun U ↦ ?_
  rw [IsFinite.SpecMap_iff]
  have := IsLocallyNoetherian.component_noetherian (X := X.left) ⟨U.1, U.2⟩
  refine Ideal.finite_toExtendedReesAlgebra (IsNoetherian.noetherian _) ?_
  obtain ⟨n, hn⟩ := IsNoetherianRing.isNilpotent_nilradical Γ(X.left, U.1)
  exact ⟨n, le_bot_iff.mp
    ((Ideal.pow_right_mono (IdealSheafData.le_def.mp hI _) n).trans hn.le)⟩

/-- For a proper `k`-scheme `X` and a nilpotent ideal sheaf `I`, `D_I X ⟶ 𝔸¹_k` is proper. -/
lemma isProper_deformationSpaceToAffineLine [IsProper X.hom] (hI : I ≤ X.left.nilradical) :
    IsProper (deformationSpaceToAffineLine X I) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have := isFinite_deformationSpaceToPolynomialSpec X hI
  have : IsProper (AffineSpace.map (ULift.{u} (Fin 1)) X.hom) :=
    MorphismProperty.of_isPullback (P := @IsProper) (AffineSpace.isPullback_map X.hom).flip
      inferInstance
  rw [deformationSpaceToAffineLine]
  infer_instance

/-- For a proper `k`-scheme `X` and a nilpotent ideal sheaf `I`, the total space of the
deformation to the normal cone is proper over the trait. -/
lemma isProper_deformationTotalToTrait [IsProper X.hom] (hI : I ≤ X.left.nilradical) :
    IsProper (deformationTotalToTrait X I k') :=
  MorphismProperty.pullback_snd _ _ (isProper_deformationSpaceToAffineLine X hI)

/-- The ideal of a rational point of a one-point scheme is nilpotent. -/
lemma ker_le_nilradical {b : RationalPoint X} (hb : Set.range b.left.base = Set.univ) :
    b.left.ker ≤ X.left.nilradical := by
  rw [← IdealSheafData.vanishingIdeal_top, ← IdealSheafData.le_support_iff_le_vanishingIdeal]
  exact fun x _ ↦ b.left.range_subset_ker_support (hb ▸ Set.mem_univ x)

/-- The deformation to the normal cone of a rational point of a proper one-point `k`-scheme is
proper over the trait. -/
lemma isProper_deformationTotalToTrait_ker [IsProper X.hom] {b : RationalPoint X}
    (hb : Set.range b.left.base = Set.univ) : IsProper (deformationTotalToTrait X b.left.ker k') :=
  isProper_deformationTotalToTrait X k' (ker_le_nilradical X hb)

end AlgebraicGeometry.ProEtale.CondensedRing
