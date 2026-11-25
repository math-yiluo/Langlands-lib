/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FinitePullbackTensorRep.FinitePullbackTensorRepresentativeData
import WeilConjectures.SmoothPurity.FinitePullbackTensorRep.FinitePullbackTensorRepresentativeSquare
import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorKFlatDiagrams
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Extending finite tensor representatives beyond flat terms

Source: Stacks Tags 06YS and 07A4.
(blueprint: lem-pur-finite-pullback-tensor-kflat-representatives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u v w
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures
attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  Functor.mapDerivedCategory finitePullbackTensorConstruction
  finiteIntrinsicClosed finiteIntrinsicTensorModels
  proEtaleTensorPullbackTotalIso proEtaleTensorPullbackTotal
  proEtaleOrdinaryTensorPullback SheafOfModules.monoidalCategory
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  finiteIntrinsicDerivedTensor
  coefficientTotalTensor coefficientKFlatInclusion coefficientFiniteInternalHom
  FinitePullbackTensorRep.totalTensor
attribute [local semireducible] FinitePullbackTensorRep.pull
attribute [local implicit_reducible] FinitePullbackTensorRep.pull
  CategoryTheory.Functor.map₂HomologicalComplex
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
attribute [local instance] FinitePullbackTensorRep.modules_abelian
  FinitePullbackTensorRep.modules_derived FinitePullbackTensorRep.ordinary_additive
  FinitePullbackTensorRep.ordinary_limits FinitePullbackTensorRep.ordinary_colimits
attribute [local implicit_reducible] FinitePullbackTensorRep.modules_abelian
  FinitePullbackTensorRep.modules_derived

private theorem natTrans_eq_of_resolution {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (a b : F ⟶ G) {A B : C} (m : A ⟶ B) [IsIso (F.map m)]
    (h : a.app A = b.app A) : a.app B = b.app B := by
  apply (cancel_epi (F.map m)).1
  rw [a.naturality, b.naturality, h]

private theorem heq_comp_eqToIso {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (h : F = G) (X : C) {V : D}
    (a : V ⟶ F.obj X) (b : V ⟶ G.obj X) (ha : HEq a b) :
    a ≫ (eqToIso h).hom.app X = b := by
  subst h
  cases ha
  simp

private theorem finiteRepresentative_eq (W : Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (normalizedDVRModules l E W n) ℤ)
    (hP : proEtaleFlatRepresentatives W (integralCoefficientCommRingSheaf l E W n) P)
    (hQ : proEtaleFlatRepresentatives W (integralCoefficientCommRingSheaf l E W n) Q) :
    (FinitePullbackTensorRep.representative l E W n P Q hP hQ).hom =
      ((finiteIntrinsicTensorModels l E W n).iso (ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) (finiteIntrinsicClosed l E W n)
        P Q hP.1 hQ.1).hom := by
  let h := (pullbackTensorFiniteRepresentative_existsUnique W
    (integralCoefficientCommRingSheaf l E W n) (finiteIntrinsicClosed l E W n)
    (finiteIntrinsicTensorModels l E W n)).exists.choose_spec
  unfold FinitePullbackTensorRep.representative pullbackTensorFiniteModelIso
  exact heq_comp_eqToIso h.1 _ _ _ (h.2 ⟨P, hP⟩ ⟨Q, hQ⟩)

-- The two-input resolution argument includes the full tensor naturality square.
/-- The prescribed finite tensor square on arbitrary K-flat complexes whose ordinary
pullbacks are K-flat. Source: Stacks 06YS and 07A4
(blueprint: lem-pur-finite-pullback-tensor-kflat-representatives).
Proof: regard both sides as natural isomorphisms on pairs of K-flat complexes whose
pullbacks are K-flat. The tensor-model comparisons are natural on this full subcategory.
Resolve each input by a flat-term K-flat complex. Its ordinary pullback is again a
flat-term K-flat complex. The existing flat representative square gives equality at
the resolved pair, because its uniquely normalized representative is the restriction
of the prescribed finite tensor model. The localization of each resolution is an
isomorphism. Naturality of the tensor models makes the localized total tensor map
invertible too. Naturality of the two square composites and cancellation transport
the equality to the original pair. No terms of that pair need be flat. -/
theorem finitePullbackTensor_ringed_kflat_square {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (P Q : CochainComplex (normalizedDVRModules l E Y n) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E Y n) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E Y n) Q)
    (hFP : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E X n)
      ((FinitePullbackTensorRep.pull l E f n).obj P))
    (hFQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E X n)
      ((FinitePullbackTensorRep.pull l E f n).obj Q)) :
    (finiteDerivedPullback l E n f).map
        ((finiteIntrinsicTensorModels l E Y n).iso (ProEt.topology Y)
          (integralCoefficientCommRingSheaf l E Y n) (finiteIntrinsicClosed l E Y n)
          P Q hP hQ).hom ≫
      ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY)
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
      (finiteIntrinsicDerivedTensor l E X n).map (Prod.mkHom
        ((FinitePullbackTensorRep.factors l E f n).hom.app P)
        ((FinitePullbackTensorRep.factors l E f n).hom.app Q)) =
    (FinitePullbackTensorRep.factors l E f n).hom.app
        (FinitePullbackTensorRep.tensor l E Y n P Q) ≫
      DerivedCategory.Q.map (FinitePullbackTensorRep.comparison l E f n P Q) ≫
      ((finiteIntrinsicTensorModels l E X n).iso (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n) (finiteIntrinsicClosed l E X n)
        ((FinitePullbackTensorRep.pull l E f n).obj P)
        ((FinitePullbackTensorRep.pull l E f n).obj Q) hFP hFQ).hom := by
  let R := integralCoefficientCommRingSheaf l E Y n
  let S := integralCoefficientCommRingSheaf l E X n
  let F := FinitePullbackTensorRep.pull l E f n
  let LF := finiteDerivedPullback l E n f
  let TY := finiteIntrinsicDerivedTensor l E Y n
  let PR : ObjectProperty (CochainComplex (normalizedDVRModules l E Y n) ℤ) :=
    fun K ↦ CochainComplex.IsKFlatIndependentCoefficients (R := R) K ∧
      CochainComplex.IsKFlatIndependentCoefficients (R := S) (F.obj K)
  let i := PR.ι
  let q := i ⋙ DerivedCategory.Q
  let rY := finiteTensorModelOnKFlatFamily l E Y n i (fun A ↦ A.property.1)
  let t := (i.prod i) ⋙ FinitePullbackTensorRep.totalTensor l E Y n
  obtain ⟨L, N, hL, hN⟩ := finitePullbackTensor_kflat_diagrams l E f n PR
    (fun _ h ↦ h.1) (fun _ h ↦ h.2)
  have hgood (K : CochainComplex (normalizedDVRModules l E Y n) ℤ)
      (hK : proEtaleFlatRepresentatives Y R K) : PR K := by
    refine ⟨hK.1, ?_⟩
    exact ((proEtaleCanonicalTensorPullback f R S
      (pullbackTensorCoefficientIso l E f n)
      (pullbackTensorFiniteModel l E Y n) (pullbackTensorFiniteModel l E X n)).1 K hK).1
  have hflat (A B : CochainComplex (normalizedDVRModules l E Y n) ℤ)
      (hA : proEtaleFlatRepresentatives Y R A)
      (hB : proEtaleFlatRepresentatives Y R B) :
      L.app (⟨A, hgood A hA⟩, ⟨B, hgood B hB⟩) =
        N.app (⟨A, hgood A hA⟩, ⟨B, hgood B hB⟩) := by
    obtain ⟨hA', hB', h⟩ := FinitePullbackTensorRep.square l E f n A B hA hB
    rw [finiteRepresentative_eq, finiteRepresentative_eq] at h
    rw [hL, hN]
    exact h
  obtain ⟨A, a, hA, flatA, ha, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) P
  obtain ⟨B, b', hB, flatB, hb, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) Q
  have hAf : proEtaleFlatRepresentatives Y R A := ⟨hA, fun k ↦
    (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R (A.X k)).symm
      (flatA k)⟩
  have hBf : proEtaleFlatRepresentatives Y R B := ⟨hB, fun k ↦
    (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R (B.X k)).symm
      (flatB k)⟩
  let AB : PR.FullSubcategory × PR.FullSubcategory :=
    (⟨A, hgood A hAf⟩, ⟨B, hgood B hBf⟩)
  let PQ : PR.FullSubcategory × PR.FullSubcategory :=
    (⟨P, ⟨hP, hFP⟩⟩, ⟨Q, ⟨hQ, hFQ⟩⟩)
  let m : AB ⟶ PQ :=
    Prod.mkHom (ObjectProperty.homMk a) (ObjectProperty.homMk b')
  have : IsIso (DerivedCategory.Q.map a) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ a).2 ha
  have : IsIso (DerivedCategory.Q.map b') :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ b').2 hb
  have : IsIso (((q.prod q) ⋙ TY ⋙ LF).map m) := by
    change IsIso (LF.map (TY.map
      (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b'))))
    exact (inferInstance : IsIso
      ((LF.mapIso (TY.mapIso ((asIso (DerivedCategory.Q.map a)).prod
        (asIso (DerivedCategory.Q.map b'))))).hom))
  have : IsIso ((t ⋙ DerivedCategory.Q ⋙ LF).map m) := by
    apply (NatIso.isIso_map_iff (isoWhiskerRight rY LF) m).2
    change IsIso (((q.prod q) ⋙ TY ⋙ LF).map m)
    infer_instance
  have h : L.app (⟨P, ⟨hP, hFP⟩⟩, ⟨Q, ⟨hQ, hFQ⟩⟩) =
      N.app (⟨P, ⟨hP, hFP⟩⟩, ⟨Q, ⟨hQ, hFQ⟩⟩) := by
    exact natTrans_eq_of_resolution (F := t ⋙ DerivedCategory.Q ⋙ LF) L N m (hflat A B hAf hBf)
  rw [hL, hN] at h
  exact h

end WeilConjectures
