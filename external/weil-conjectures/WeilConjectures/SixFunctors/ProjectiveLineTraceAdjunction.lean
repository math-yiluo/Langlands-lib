/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProjectiveLineTraceModel
import WeilConjectures.SixFunctors.FiniteTraceCounitComparison
import WeilConjectures.SixFunctors.KernelCounitTraceChange
import WeilConjectures.SixFunctors.ProjectiveLinePresentedKernelAdjunction
import WeilConjectures.SixFunctors.ProjectiveLineTraceNormalization

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

private theorem tensor_adjunction_transport
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (P : D ⥤ C) (T : C ⥤ C ⥤ C) (β : T ≅ T.flip)
    (B : C) (a : B ≅ B) (adj₀ : F ⊣ P ⋙ T.obj B)
    (ε : (P ⋙ T.obj B) ⋙ F ⟶ 𝟭 D) (hε : adj₀.counit = ε) :
    ∃ adj : F ⊣ P ⋙ T.flip.obj B, ∀ K : D,
      adj.counit.app K = F.map (β.inv.app B |>.app (P.obj K)) ≫
        F.map ((T.map a.hom).app (P.obj K)) ≫ ε.app K := by
  subst ε
  let θ := Functor.isoWhiskerLeft P (T.mapIso a.symm)
  let σ := Functor.isoWhiskerLeft P (β.app B)
  refine ⟨(adj₀.ofNatIsoRight θ).ofNatIsoRight σ, ?_⟩
  intro K
  rfl

private theorem normalized_tensor_adjunction
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (P : D ⥤ C) (T : C ⥤ C ⥤ C) (β : T ≅ T.flip)
    (B : C) (a : B ≅ B) (adj₀ : F ⊣ P ⋙ T.obj B)
    (ε₀ ε₁ : (P ⋙ T.obj B) ⋙ F ⟶ 𝟭 D)
    (ε : (P ⋙ T.flip.obj B) ⋙ F ⟶ 𝟭 D)
    (hε : adj₀.counit = ε₀)
    (hchange : ∀ K : D, F.map ((T.map a.hom).app (P.obj K)) ≫ ε₀.app K = ε₁.app K)
    (hcompare : ∀ K : D, F.map (β.inv.app B |>.app (P.obj K)) ≫ ε₁.app K = ε.app K) :
    ∃ adj : F ⊣ P ⋙ T.flip.obj B, adj.counit = ε := by
  obtain ⟨adj, hadj⟩ := tensor_adjunction_transport F P T β B a adj₀ ε₀ hε
  refine ⟨adj, ?_⟩
  ext K
  rw [hadj K, hchange K, hcompare K]

/-- Assemble the normalized kernel counit into the prescribed finite trace adjunction. -/
private theorem exists_finiteTraceAdjunction_of_kernel
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    (B : DerivedCategoryModule A X) (D : TraceDiagonalDatum A q B)
    (adj₀ : rightDerivedLowerShriek (ModuleCat.{u + 1} A) q ⊣
      CoordinateTrace.pull A q ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj B)
    (hε : adj₀.counit = SfDiagonalKernel.counit A D)
    (τ : (ordinaryFinitePushforward A q).obj B ⟶ ordinaryFiniteUnit A Y)
    (s : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).obj B ⟶
      derivedTensorUnit (ModuleCat.{u + 1} A) Y)
    (htrace : D.trace = s)
    (hNorm : ∃ a : B ≅ B,
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).map a.hom ≫ s =
        (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) q).hom.app B ≫
          τ ≫ (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).hom) :
    ∃ adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) q ⊣
      ordinaryFiniteTwistedPullback A q B,
      adj.counit = finiteP1TraceCounit A q B τ := by
  obtain ⟨a, ha⟩ := hNorm
  have ht : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).map a.hom ≫ D.trace =
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).hom.app B ≫
        τ ≫ (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).hom := by
    exact (congrArg (fun z ↦
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).map a.hom ≫ z) htrace).trans ha
  let τ' : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).obj B ⟶
      derivedTensorUnit (ModuleCat.{u + 1} A) Y :=
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).hom.app B ≫
      τ ≫ (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).hom
  let D' := kernelDatumWithTrace A q B D τ'
  obtain ⟨htr, hmap⟩ := kernelCounit_traceChange A q B D a τ' ht
  exact normalized_tensor_adjunction
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q) (CoordinateTrace.pull A q)
    (derivedTensor (ModuleCat.{u + 1} A) X) (derivedTensorSymmetry (ModuleCat.{u + 1} A) X)
    B a adj₀ (SfDiagonalKernel.counit A D) (SfDiagonalKernel.counit A D')
    (finiteP1TraceCounit A q B τ) hε hmap
    (finiteP1TraceCounit_kernel_comparison A q B D' τ htr)

/-- Construct the adjunction with the canonical proper compactification instance. -/
private theorem canonical_presentedFiniteP1TraceAdjunction
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
      ArbitraryBaseFiniteP1Splitting A N hA t T hT)
    (hbc : ArbitraryBaseFiniteP1BaseChange A N hA t d)
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    (e : X ≅ ProjectiveLine Y) (w : e.hom ≫ (ProjectiveLine Y ↘ Y) = q)
    (hY : IsUnit (N : Γ(Y, ⊤))) (hdiag : finiteP1DiagonalProperty A N hA t d Y hY) :
    ∃ adj : R(q)_![ModuleCat.{u + 1} A] ⊣
        ordinaryFiniteTwistedPullback A q ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧),
      adj.counit = presentedFiniteP1Counit A N hA t q e w hY (d Y hY) := by
  obtain ⟨κ, adj₀, hadj₀⟩ := exists_presentedFiniteP1KernelAdjunction
    A N hN hA t d hbc q e w hY hdiag
  exact exists_finiteTraceAdjunction_of_kernel A q _ _ adj₀ hadj₀
    (presentedFiniteP1Trace A N hA t q e w hY (d Y hY))
    (SfP1Transport.trace A N hA t q e w hY (d Y hY).trace)
    (SfP1Transport.datum_trace A N hA t q e w hY (d Y hY).trace κ)
    (exists_presentedFiniteP1TraceNormalization A N hA t q e w hY (d Y hY))

/-- The normalized finite projective-line trace is the counit of twisted pullback duality.
Source: blueprint sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, (G6), (G7), both triangle calculations.
(auxiliary; not a blueprint node)

Proof: take the explicit transported trace-diagonal datum associated to the supported
class in the diagonal property. The two integral comparisons conjugate the given
ordinary identities to the compact-support identities. The finite Tate sheaf is a
lisse line, so the existing diagonal-kernel triangle theorem gives both triangles
and hence an adjunction with the kernel counit. Direct image along the presentation
is an equivalence. Lift the discrepancy between its two coefficient identifications
to an automorphism of the shifted line, and transport the right adjoint through its
inverse tensor action and the tensor symmetry. Projection naturality gives the kernel
counit for the adjusted trace. Proper projection coherence, braiding naturality and
the unitors identify this with the prescribed inverse-projection counit. Every map
is the constructed map; no arbitrary trace or exceptional base-change map is chosen.
The constructions apply on unbounded categories and also to empty bases and the zero ring. -/
theorem exists_presentedFiniteP1TraceAdjunction
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
      ArbitraryBaseFiniteP1Splitting A N hA t T hT)
    (hbc : ArbitraryBaseFiniteP1BaseChange A N hA t d)
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q] [HasCompactification q]
    (e : X ≅ ProjectiveLine Y) (w : e.hom ≫ (ProjectiveLine Y ↘ Y) = q)
    (hY : IsUnit (N : Γ(Y, ⊤))) (hdiag : finiteP1DiagonalProperty A N hA t d Y hY) :
    ∃ adj : R(q)_![ModuleCat.{u + 1} A] ⊣
        ordinaryFiniteTwistedPullback A q ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧),
      adj.counit = presentedFiniteP1Counit A N hA t q e w hY (d Y hY) := by
  exact canonical_presentedFiniteP1TraceAdjunction A N hN hA t d hbc q e w hY hdiag

end AlgebraicGeometry.Etale
