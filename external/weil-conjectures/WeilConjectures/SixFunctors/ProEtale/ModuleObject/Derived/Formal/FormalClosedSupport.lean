/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Retract
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.Integral.IntegralResidueTensorPresentation
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.ProEtaleFiniteProjectiveDualizable
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.ProEtalePullbackInternalHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHom
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeInternalHomColimits
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
import all WeilConjectures.CategoryTheory.ModuleObjects.Free
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
import all WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

/-!
# Sections with support in a closed subscheme

Source: blueprint `sec-six-functors-basics/sk-lem-formal-closed-support`,
using the derived closed-support and stratum-Hom interfaces
(blueprint: lemma-sections-support-closed-subscheme).

The support functors are the canonical kernel and coefficient-compatible inverse-image
constructions from `FormalClosedSupportAdjunction`. The stratum formula uses the actual
extension `i_*u_!L`, the internal dual `Hom(L, Λ_S)`, and derived global sections. Finite
local projectivity means a retract of a finite free module on a pro-étale cover.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open scoped CategoryTheory.Obj

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
  CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- Global sections of a coefficient module, with its underlying abelian group.
Source: blueprint `lemma-sections-support-closed-subscheme`, clause (2), the functor Γ(S,-)
(blueprint: lemma-sections-support-closed-subscheme). The right derived functor of this composite is
RΓ(S,-); the scalar action is retained by the input module before taking sections. -/
noncomputable def formalClosedSupportSections (X : Scheme.{u}) :
    FormalSupportModules Λ X ⥤ Ab.{u + 1} :=
  Mod.forget (condensedRingObj Λ X) ⋙ Sheaf.Γ (Scheme.ProEt.topology X) Ab.{u + 1}

/-- Sections are additive, since both forgetful and global-sections functors preserve
finite products. Source: blueprint `lemma-sections-support-closed-subscheme`, clause (2)
(blueprint: lemma-sections-support-closed-subscheme). -/
noncomputable instance formalClosedSupportSections_additive (X : Scheme.{u}) :
    (formalClosedSupportSections Λ X).Additive :=
  Functor.additive_of_preserves_binary_products
    (Mod.forget (condensedRingObj Λ X) ⋙ Sheaf.Γ (Scheme.ProEt.topology X) Ab.{u + 1})

@[irreducible] private noncomputable def lowerStarSectionsIso {Y X : Scheme.{u}} (f : Y ⟶ X) :
    lowerStar Λ f ⋙ formalClosedSupportSections Λ X ≅ formalClosedSupportSections Λ Y := by
  unfold formalClosedSupportSections
  change ((lowerStar Λ f ⋙ Mod.forget (condensedRingObj Λ X)) ⋙
      Sheaf.Γ (Scheme.ProEt.topology X) Ab.{u + 1}) ≅ _
  rw [lowerStar_comp_forget]
  exact Functor.isoWhiskerLeft (Mod.forget (condensedRingObj Λ Y))
    (ProEtale.globalSectionsLowerStarIso Ab.{u + 1} f)

@[irreducible] private noncomputable def derivedLowerStarSectionsIso
    {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (lowerStar Λ f).rightDerivedFunctor ⋙
        (formalClosedSupportSections Λ X).rightDerivedFunctor ≅
      (formalClosedSupportSections Λ Y).rightDerivedFunctor := by
  have : (lowerStar Λ f).PreservesKInjectiveComplexes :=
    (formalSupportPullbackAdjunction Λ f).preservesKInjectiveComplexes
  exact Functor.rightDerivedFunctorCompIso' _ _ (lowerStarSectionsIso Λ f)

@[irreducible] private noncomputable def closedDerivedHomIso {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (A : DerivedCategory (FormalSupportModules Λ Z)) :
    let := closedSupport_lowerStarExact Λ i j hij
    (derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj A)) ≅
      (closedSupport Λ i j).rightDerivedFunctor ⋙ (derivedHom Λ Z).obj (op A) ⋙
        (lowerStar Λ i).mapDerivedCategory := by
  classical
  let := closedSupport_lowerStarExact Λ i j hij
  exact Classical.choice (by
    obtain ⟨_, _, c, _, _, _, _, hc⟩ := openClosedInternalHomFormulas Λ i j hij
    exact ⟨NatIso.ofComponents (c A) (by
      intro N N' f
      have h := hc A A N N' (𝟙 A) f
      rw [(lowerStar Λ i).mapDerivedCategory.map_id, op_id, (derivedHom Λ X).map_id,
        NatTrans.id_app, Category.id_comp, op_id, (derivedHom Λ Z).map_id,
        NatTrans.id_app, Category.id_comp] at h
      exact h)⟩)

@[irreducible] private noncomputable def openDerivedHomIso {S Z : Scheme.{u}}
    (v : S ⟶ Z) [IsOpenImmersion v] [QuasiCompact v]
    (A : DerivedCategory (FormalSupportModules Λ S)) :
    (derivedHom Λ Z).obj (op ((openImmersionLowerShriek Λ v).mapDerivedCategory.obj A)) ≅
      (supportPullback Λ v).mapDerivedCategory ⋙ (derivedHom Λ S).obj (op A) ⋙
        (lowerStar Λ v).rightDerivedFunctor := by
  classical
  let T : TopologicalSpace.Closeds Z :=
    ⟨(Set.range v)ᶜ, v.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let I := Scheme.IdealSheafData.vanishingIdeal T
  have hIv : Set.range I.subschemeι.base = (Set.range v.base)ᶜ := by
    change Set.range I.subschemeι = (T : Set Z)
    simp [I]
  exact Classical.choice (by
    obtain ⟨_, o, _, _, _, _, ho, _⟩ := openClosedInternalHomFormulas Λ I.subschemeι v hIv
    exact ⟨NatIso.ofComponents (o A) (by
      intro N N' f
      have h := ho A A N N' (𝟙 A) f
      rw [(openImmersionLowerShriek Λ v).mapDerivedCategory.map_id, op_id,
        (derivedHom Λ Z).map_id, NatTrans.id_app, Category.id_comp, op_id,
        (derivedHom Λ S).map_id, NatTrans.id_app, Category.id_comp] at h
      exact h)⟩)

private theorem coverRetract_dualizable
    (S : Scheme.{u}) (L : FormalSupportModules Λ S)
    (hL : ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S,
      ∀ c : 𝒰.I₀, ∃ n : ℕ,
        Nonempty (Retract ((formalSupportPullback Λ (𝒰.f c)).obj L)
          (Mod.finiteFree (condensedRingObj Λ (𝒰.X c)) n))) :
    IsDualizable L := by
  classical
  obtain ⟨𝒰, h𝒰⟩ := hL
  let t := MonoidalClosed.ihomUnitTensorToIhom L L
  have ht : IsIso t := by
    apply ProEtale.isIso_mapMod_of_cover 𝒰 (condensedRingObj Λ S) t
    intro c
    have : WeaklyEtale (𝒰.f c) :=
      Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ (.mk c)
    obtain ⟨n, ⟨r⟩⟩ := h𝒰 c
    have hd : IsDualizable ((supportPullback Λ (𝒰.f c)).obj L) :=
      finiteFree_retract_isDualizable Λ (𝒰.X c) n _ r.i r.r r.retract
    obtain ⟨hd⟩ := hd
    let M := (supportPullback Λ (𝒰.f c)).obj L
    let : ExactPairing Mᘁ M := BraidedCategory.exactPairing_swap M Mᘁ
    have : IsIso (MonoidalClosed.ihomUnitTensorToIhom M M) :=
      MonoidalClosed.isIso_ihomUnitTensorToIhom Mᘁ M M
    have := supportPullback_ihomComparison_isIso Λ (𝒰.f c) L
    have : IsIso ((supportPullback Λ (𝒰.f c)).map t) :=
      Functor.Monoidal.isIso_map_ihomUnitTensorToIhom_of_ihomComparison _ _ _
    have : IsIso ((Mod.comap
        (asIso (condensedPullbackHom Λ (𝒰.f c))).inv).map
          (((ProEtale.upperStar Ab.{u + 1} (𝒰.f c)).mapMod _).map t)) := this
    exact isIso_of_reflects_iso _
      (Mod.comap (asIso (condensedPullbackHom Λ (𝒰.f c))).inv)
  let := MonoidalClosed.exactPairingOfIsIso L
  let := BraidedCategory.exactPairing_swap ((ihom L).obj (𝟙_ _)) L
  exact ⟨⟨(ihom L).obj (𝟙_ _)⟩⟩

@[irreducible] private noncomputable def finiteProjectiveDerivedHomIso
    (S : Scheme.{u}) (L : FormalSupportModules Λ S) (hL : IsDualizable L) :
    (derivedHom Λ S).obj
        (op ((DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj L)) ≅
      (derivedTensor Λ S).obj
        ((DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj
          ((ihom L).obj (𝟙_ (FormalSupportModules Λ S)))) := by
  let := hL.some
  let : ExactPairing Lᘁ L := BraidedCategory.exactPairing_swap L Lᘁ
  let D := (ihom L).obj (𝟙_ (FormalSupportModules Λ S))
  let eT : ihom L ≅ tensorLeft D :=
    MonoidalClosed.ihomIsoTensorLeft Lᘁ L ≪≫
      (curriedTensor _).mapIso (MonoidalClosed.ihomObjUnitIso Lᘁ L).symm
  have : PreservesFiniteLimits (tensorLeft D) := preservesFiniteLimits_of_natIso eT
  let a := (ihom.adjunction L).derivedAdjunction.ofNatIsoLeft (derivedTensorSingleIso L)
  exact (derivedTensorHomAdjunction Λ
      ((DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj L)).rightAdjointUniq a ≪≫
    Functor.rightDerivedFunctorNatIso eT ≪≫
    (tensorLeft D).rightDerivedFunctorIsoMapDerivedCategory ≪≫
    (tensorLeft D).leftDerivedFunctorIsoMapDerivedCategory.symm ≪≫ derivedTensorSingleIso D

/-- The closed-support adjunction, fiber triangle and stratum formula.
Source: blueprint `sec-six-functors-basics/sk-lem-formal-closed-support`, clauses (1)--(2)
(blueprint: lemma-sections-support-closed-subscheme).

The ordinary adjunction is normalized by the existing support-kernel inclusion;
`rightAdjoint_eq` specifies its derived adjunction, rather than an arbitrary rescaling.
`globalRHom` specifies the K-injective Hom-complex comparison of clause (1).
In `stratum`, the explicit covering-and-retract predicate is finite local projectivity:
after restriction to each member, L is a direct summand of Λ^n. The dual is the ordinary
internal Hom from L to the tensor unit, namely Λ_S. The displayed natural isomorphism of
functors in K is RHom_X(i_*u_!L,K) ≅ RΓ(S,L^∨ ⊗ u^*RΓ_Z K). Finite local projectivity makes
the ordinary tensor product in the source equal to the derived tensor used here. -/
structure FormalClosedSupportAssertions {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) where
  ordinaryAdjunction : lowerStar Λ i ⊣ formalClosedSupport Λ i j
  counit_normalization :
    ∀ M : FormalSupportModules Λ X,
      (formalSupportKernelComparison Λ i j).app M ≫ ordinaryAdjunction.counit.app M =
        (formalSupportKernelInclusion Λ j).app M
  rightAdjoint :
    letI := ordinaryAdjunction.leftAdjoint_preservesColimits
    (lowerStar Λ i).mapDerivedCategory ⊣
      (formalClosedSupport Λ i j).rightDerivedFunctor
  rightAdjoint_eq :
    letI := ordinaryAdjunction.leftAdjoint_preservesColimits
    rightAdjoint = ordinaryAdjunction.mapDerivedCategoryRightDerivedAdjunction
  fiber :
    letI := ordinaryAdjunction.leftAdjoint_preservesColimits
    ∃ δ : (formalSupportPullback Λ j).mapDerivedCategory ⋙
        (lowerStar Λ j).rightDerivedFunctor ⟶
        ((formalClosedSupport Λ i j).rightDerivedFunctor ⋙
          (lowerStar Λ i).mapDerivedCategory) ⋙
          shiftFunctor (DerivedCategory (FormalSupportModules Λ X)) (1 : ℤ),
      ∀ K : DerivedCategory (FormalSupportModules Λ X),
        Triangle.mk (rightAdjoint.counit.app K)
          (((formalSupportPullbackAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction).unit.app
            K)
          (δ.app K) ∈
          Pretriangulated.distinguishedTriangles
  globalRHom :
    ∀ (A : CochainComplex (FormalSupportModules Λ Z) ℤ)
      (I : CochainComplex (FormalSupportModules Λ X) ℤ) [I.IsKInjective],
      ∃ e : CochainComplex.HomComplex
          (((lowerStar Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) I ≅
        CochainComplex.HomComplex A
          (((formalClosedSupport Λ i j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I),
        ∀ (n : ℤ)
          (a : CochainComplex.HomComplex.Cochain
            (((lowerStar Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) I n)
          (p q : ℤ) (hpq : p + n = q),
          (e.hom.f n a) ⟨p, q, hpq⟩ =
            ordinaryAdjunction.homEquiv (A.X p) (I.X q) (a ⟨p, q, hpq⟩)
  stratum :
    ∀ {S : Scheme.{u}} (u : S ⟶ Z) [IsOpenImmersion u]
      (L : FormalSupportModules Λ S),
      (∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S,
        ∀ c : 𝒰.I₀, ∃ n : ℕ,
          Nonempty (Retract ((formalSupportPullback Λ (𝒰.f c)).obj L)
            (Mod.finiteFree (condensedRingObj Λ (𝒰.X c)) n))) →
      Nonempty
        ((derivedHom Λ X).obj
            (op ((DerivedCategory.singleFunctor (FormalSupportModules Λ X) 0).obj
              ((lowerStar Λ i).obj ((openImmersionLowerShriek Λ u).obj L)))) ⋙
            (formalClosedSupportSections Λ X).rightDerivedFunctor ≅
          (formalClosedSupport Λ i j).rightDerivedFunctor ⋙
            (formalSupportPullback Λ u).mapDerivedCategory ⋙
            (derivedTensor Λ S).obj
              ((DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj
                ((ihom L).obj (𝟙_ (FormalSupportModules Λ S)))) ⋙
            (formalClosedSupportSections Λ S).rightDerivedFunctor)

/-- Sections with support in a closed subscheme: derived adjunction, fiber formula, and the
extension-by-zero stratum Hom formula.
Source: blueprint `sec-six-functors-basics/sk-lem-formal-closed-support`, clauses (1)--(2)
(blueprint: lemma-sections-support-closed-subscheme).

Proof:
1. Apply lemma-sections-support-closed-subscheme in the standing-scheme setting. Its derived
adjunction, normalized by the support-kernel inclusion in
`formal_closed_support_adjunction`, gives `ordinaryAdjunction`, `counit_normalization`,
`rightAdjoint`, `rightAdjoint_eq` and `globalRHom`. Its natural localization triangle gives
`fiber`. Applying exact i^* and i^*i_* = id identifies RΓ_Z K with i^* of the fiber of the
canonical unit K → Rj_*j^*K. These give every assertion of clause (1).
2. Apply lemma-sections-support-closed-subscheme--3 to u and the finite locally projective L.
The identity a_! = i_*u_! and the closed-support adjunction first give
RHom_X(i_*u_!L,K) ≅ RHom_Z(u_!L,RΓ_Z K). The exact open extension adjunction gives
RHom_S(L,u^*RΓ_Z K). Locally L is a retract of a finite free module, so its dual is flat
and Hom(L,-) = L^∨ ⊗ - is exact. The internal Hom and global-section comparison therefore
identify the last expression with RΓ(S,L^∨ ⊗ u^*RΓ_Z K). All comparisons are natural in K,
which gives the functor isomorphism in `stratum`. -/
theorem formalClosedSupportAssertions (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    {Z U X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    Nonempty (FormalClosedSupportAssertions Λ i j hij) := by
  classical
  have _ := hpℓ
  have hji : Set.range j = (Set.range i)ᶜ := by
    rw [hij, compl_compl]
  obtain ⟨_, _, a, hn, _, _, _, hhom, hc, b, c, δ, hb, hcc, htri, _⟩ :=
    formal_closed_support_adjunction Λ i j hji
  let := hc
  refine ⟨{
    ordinaryAdjunction := a
    counit_normalization := hn
    rightAdjoint := a.mapDerivedCategoryRightDerivedAdjunction
    rightAdjoint_eq := rfl
    fiber := ?_
    globalRHom := ?_
    stratum := ?_ }⟩
  · subst b
    subst c
    exact ⟨δ, htri⟩
  · exact hhom
  · intro S v hv L hL
    have : IsLocallyNoetherian X :=
      LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    have : CompactSpace X :=
      QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
    have : IsNoetherian X := ⟨⟩
    have : TopologicalSpace.NoetherianSpace Z :=
      i.isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
    have : TopologicalSpace.NoetherianSpace S :=
      v.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
    have : QuasiCompact v := inferInstance
    let A := (DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj L
    let B := (DerivedCategory.singleFunctor (FormalSupportModules Λ Z) 0).obj
      ((openImmersionLowerShriek Λ v).obj L)
    let eI := ((lowerStar Λ i).mapDerivedCategorySingleFunctor 0).app
      ((openImmersionLowerShriek Λ v).obj L)
    let eV := ((openImmersionLowerShriek Λ v).mapDerivedCategorySingleFunctor 0).app L
    let eC : (formalClosedSupport Λ i j).rightDerivedFunctor ≅
        (closedSupport Λ i j).rightDerivedFunctor :=
      (a.mapDerivedCategoryRightDerivedAdjunction).rightAdjointUniq
        (closedSupportDerivedAdjunction Λ i j hij)
    let eS : (lowerStar Λ i).mapDerivedCategory ⋙
        (formalClosedSupportSections Λ X).rightDerivedFunctor ≅
        (formalClosedSupportSections Λ Z).rightDerivedFunctor :=
      Functor.isoWhiskerRight
        (lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory.symm _ ≪≫
        derivedLowerStarSectionsIso Λ i
    let eClosed : (derivedHom Λ X).obj
        (op ((DerivedCategory.singleFunctor (FormalSupportModules Λ X) 0).obj
          ((lowerStar Λ i).obj ((openImmersionLowerShriek Λ v).obj L)))) ⋙
          (formalClosedSupportSections Λ X).rightDerivedFunctor ≅
        (closedSupport Λ i j).rightDerivedFunctor ⋙ (derivedHom Λ Z).obj (op B) ⋙
          (formalClosedSupportSections Λ Z).rightDerivedFunctor := Functor.isoWhiskerRight
      ((derivedHom Λ X).mapIso eI.op ≪≫ closedDerivedHomIso Λ i j hij B)
      (formalClosedSupportSections Λ X).rightDerivedFunctor ≪≫
      Functor.isoWhiskerLeft
        ((closedSupport Λ i j).rightDerivedFunctor ⋙ (derivedHom Λ Z).obj (op B)) eS
    let eOpen : (derivedHom Λ Z).obj (op B) ⋙
        (formalClosedSupportSections Λ Z).rightDerivedFunctor ≅
        (supportPullback Λ v).mapDerivedCategory ⋙ (derivedHom Λ S).obj (op A) ⋙
          (formalClosedSupportSections Λ S).rightDerivedFunctor := Functor.isoWhiskerRight
      ((derivedHom Λ Z).mapIso eV.op ≪≫ openDerivedHomIso Λ v A)
      (formalClosedSupportSections Λ Z).rightDerivedFunctor ≪≫
      Functor.isoWhiskerLeft
        ((supportPullback Λ v).mapDerivedCategory ⋙ (derivedHom Λ S).obj (op A))
        (derivedLowerStarSectionsIso Λ v)
    let eDual : (derivedHom Λ S).obj (op A) ⋙
        (formalClosedSupportSections Λ S).rightDerivedFunctor ≅
        (derivedTensor Λ S).obj
          ((DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj
            ((ihom L).obj (𝟙_ (FormalSupportModules Λ S)))) ⋙
          (formalClosedSupportSections Λ S).rightDerivedFunctor := Functor.isoWhiskerRight
      (finiteProjectiveDerivedHomIso Λ S L (coverRetract_dualizable Λ S L hL))
      (formalClosedSupportSections Λ S).rightDerivedFunctor
    exact ⟨eClosed ≪≫
      Functor.isoWhiskerLeft (closedSupport Λ i j).rightDerivedFunctor eOpen ≪≫
      Functor.isoWhiskerLeft
        ((closedSupport Λ i j).rightDerivedFunctor ⋙
          (supportPullback Λ v).mapDerivedCategory) eDual ≪≫
      Functor.isoWhiskerRight eC.symm
        ((supportPullback Λ v).mapDerivedCategory ⋙
          (derivedTensor Λ S).obj
            ((DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj
              ((ihom L).obj (𝟙_ (FormalSupportModules Λ S)))) ⋙
          (formalClosedSupportSections Λ S).rightDerivedFunctor)⟩

end AlgebraicGeometry.ProEtale.CondensedRing
