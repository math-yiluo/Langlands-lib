/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals
public import WeilConjectures.AlgebraicGeometry.SfP1IntegralTransportData
import WeilConjectures.SixFunctors.ProjectiveLinePresentedIntegrals

/-! # Compact-support integral identities of the explicit projective-line datum -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace

private theorem conjugate_identity
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {K : C} {V : D}
    (c : F.obj K ≅ V) (x : K ⟶ K) (hx : x = 𝟙 K) :
    c.inv ≫ F.map x ≫ c.hom = 𝟙 V := by
  rw [hx, F.map_id, Category.id_comp, c.inv_hom_id]

/-- The explicit transported supported datum has both compact-support integrals equal to one.
Source: blueprint latest, thm-amb-p1-adjunction.proof.md, the two diagonal integrals.
(auxiliary; not a blueprint node)

Proof: extract the supported class and the two ordinary integral identities from the
finite diagonal property. The proved comparison for the constructed datum identifies
its first and second compact-support integrals with conjugates of these ordinary
integrals. Each conjugate is identity by functoriality and cancellation of the constant
comparison isomorphism. This uses the actual constructed trace in both integrals. -/
theorem exists_presentedFiniteP1Datum_integrals
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
      ArbitraryBaseFiniteP1Splitting A N hA t T hT)
    (hbc : ArbitraryBaseFiniteP1BaseChange A N hA t d)
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    (e : X ≅ ProjectiveLine Y) (w : e.hom ≫ (ProjectiveLine Y ↘ Y) = q)
    (hY : IsUnit (N : Γ(Y, ⊤))) (hdiag : finiteP1DiagonalProperty A N hA t d Y hY) :
    ∃ κ : Ext
      ((lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine Y ↘ Y))).obj
        (ordinaryFiniteConstant A (ProjectiveLine Y)))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) N A hA) 2,
      SfDiagonalKernel.Integrals A
        (SfP1Transport.datum A N hA t q e w hY (d Y hY).trace κ)
        (CoordinateTrace.shiftedLine A (Scheme.finiteEtaleTateLine Y N A hA) 1)
        (ordinaryFiniteShiftedLinePullback A N hA t q hY).symm := by
  obtain ⟨_, κ, _, hint⟩ := hdiag
  obtain ⟨hfirst, hsecond⟩ :=
    presentedFiniteP1Datum_integral_comparison A N hA t d hbc Y X q e w hY κ
  refine ⟨κ, ?_, ?_⟩
  · exact hfirst.trans (conjugate_identity (ordinaryFinitePullback A e.hom)
      (SfP1Transport.constantComparison A e) _ (hint false).2)
  · exact hsecond.trans (conjugate_identity (ordinaryFinitePullback A e.hom)
      (SfP1Transport.constantComparison A e) _ (hint true).2)

end AlgebraicGeometry.Etale
