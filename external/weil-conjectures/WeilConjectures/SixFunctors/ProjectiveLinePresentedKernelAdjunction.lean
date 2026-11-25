/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals
public import WeilConjectures.AlgebraicGeometry.SfP1IntegralTransportData
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.SixFunctors.ProjectiveLinePresentedKernelIntegrals

/-! # Adjunction for the normalized finite trace over arbitrary bases

The supported diagonal gives a kernel adjunction. A coefficient automorphism and
proper projection coherence identify its counit with the specified presentation trace.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] SfDiagonalKernel.unit SfDiagonalKernel.counit
  derivedTensor singleFunctorObjUnitIso
  DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace

set_option allowUnsafeReducibility true in
attribute [local irreducible] rightDerivedLowerShriekOfCompactification
  instCategoryDerivedCategory

private theorem diagonalAdjunction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    (B : DerivedCategoryModule A X) (D : TraceDiagonalDatum A q B)
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hJ : Scheme.IsLisseRankOneSheaf J) (n : ℤ)
    (b : B ≅ (CoordinateTrace.pull A q).obj (CoordinateTrace.shiftedLine A J n))
    (h : SfDiagonalKernel.Integrals A D (CoordinateTrace.shiftedLine A J n) b) :
    ∃ adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) q ⊣
      CoordinateTrace.pull A q ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj B,
      adj.counit = SfDiagonalKernel.counit A D := by
  obtain ⟨hl, hr⟩ := SfDiagonalKernel.triangles A D J hJ n b h
  exact ⟨{ unit := SfDiagonalKernel.unit A D
           counit := SfDiagonalKernel.counit A D
           left_triangle_components := hl
           right_triangle_components := hr }, rfl⟩

/-- The constructed projective-line diagonal datum yields its kernel adjunction.
Source: blueprint latest, thm-amb-p1-adjunction.proof.md, both triangle calculations.
(auxiliary; not a blueprint node)

Proof: the finite diagonal property and the integral comparison give a supported class
whose constructed compact-support datum has both integrals one. Invertibility of N on
global sections implies invertibility on each stalk. The local trivialization theorem
therefore makes the finite Tate sheaf a lisse line. Apply the diagonal-kernel triangle
theorem to this line and the shifted coefficient pullback comparison. The prescribed
kernel unit and counit, with those two triangles, form the asserted adjunction. -/
theorem exists_presentedFiniteP1KernelAdjunction
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
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
      ∃ adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) q ⊣
        CoordinateTrace.pull A q ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧),
        adj.counit = SfDiagonalKernel.counit A
          (SfP1Transport.datum A N hA t q e w hY (d Y hY).trace κ) := by
  classical
  obtain ⟨κ, hInt⟩ := exists_presentedFiniteP1Datum_integrals
    A N hA t d hbc q e w hY hdiag
  have hJ : Scheme.IsLisseRankOneSheaf (Scheme.finiteEtaleTateLine Y N A hA) := by
    have hInv (y : Y) : IsUnit (N : Y.presheaf.stalk y) := by
      simpa only [map_natCast] using hY.map (Y.presheaf.germ ⊤ y (by trivial)).hom
    obtain ⟨U, hU⟩ := Scheme.finiteEtaleTateLine_localTrivial Y N hN hInv A hA
    exact ⟨U, hU⟩
  exact ⟨κ, diagonalAdjunction A q _ _
    (Scheme.finiteEtaleTateLine Y N A hA) hJ 1
    (ordinaryFiniteShiftedLinePullback A N hA t q hY).symm hInt⟩

end AlgebraicGeometry.Etale
