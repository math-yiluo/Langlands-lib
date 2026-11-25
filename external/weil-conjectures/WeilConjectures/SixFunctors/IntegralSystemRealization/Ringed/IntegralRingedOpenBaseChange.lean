/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSlicePresentation
import WeilConjectures.AlgebraicGeometry.Integral.IntegralRingedOpenPullSupport
import all WeilConjectures.Algebra.Homology.SubterminalLocal.SubterminalModuleLocalCalculus

/-! # The specified ordinary open base-change mate

Source: Stacks 03DI, 09AE; fix-prop-coherence, ordinary open comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem ordinaryOpen_unit_isIso {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (PurCompactSupport.openAdjunction (PurCompactSupport.completed l E) j).unit := by
  let R := (PurCompactSupport.completed l E).ring X
  let S := (PurCompactSupport.completed l E).ring U
  let W := ProEt.mk j
  have : Mono (terminal.from W) := by
    constructor
    intro V f g h
    apply (ProEt.forget X ⋙ Over.forget X).map_injective
    change f.left = g.left
    apply (cancel_mono j).mp
    exact (Over.w f.hom).trans (Over.w g.hom).symm
  have hu := SheafOfModules.SubterminalLocal.adj_unit_isIso.{u+1, u, u+1} R W
  let a := SheafOfModules.SubterminalLocal.adj.{u+1, u, u+1} R W
  have : (SheafOfModules.localizedModuleExtension.{u} R W).Full :=
    a.fullyFaithfulLOfIsIsoUnit.full
  have : (SheafOfModules.localizedModuleExtension.{u} R W).Faithful :=
    a.fullyFaithfulLOfIsIsoUnit.faithful
  obtain ⟨e, ⟨q⟩⟩ := proEtaleOpen_slicePresentation j R S
    ((PurCompactSupport.completed l E).pull j)
  have : (PurCompactSupport.openExtension (PurCompactSupport.completed l E) j).Full :=
    Functor.Full.of_iso q.symm
  have : (PurCompactSupport.openExtension (PurCompactSupport.completed l E) j).Faithful :=
    Functor.Faithful.of_iso q.symm
  exact Adjunction.unit_isIso_of_L_fully_faithful
    (PurCompactSupport.openAdjunction (PurCompactSupport.completed l E) j)

private theorem derivedOpen_unit_isIso {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] : IsIso (ringedOpenAdj l E j).unit := by
  have hu := ordinaryOpen_unit_isIso l E j
  let b := PurCompactSupport.openAdjunction (PurCompactSupport.completed l E) j
  have hQ (P : CochainComplex (scalarReductionSource l E U) ℤ) :
      IsIso ((ringedOpenAdj l E j).unit.app (DerivedCategory.Q.obj P)) := by
    have hi (n : ℤ) : IsIso (((b.mapHomologicalComplex (.up ℤ)).unit.app P).f n) :=
      inferInstanceAs (IsIso (b.unit.app (P.X n)))
    have := HomologicalComplex.Hom.isIso_of_components
      ((b.mapHomologicalComplex (.up ℤ)).unit.app P)
    simp only [ringedOpenAdj, PurCompactSupport.openDerivedAdjunction,
      Adjunction.localization_unit_app]
    infer_instance
  have (M : Integral l E U) : IsIso ((ringedOpenAdj l E j).unit.app M) :=
    (NatTrans.isIso_app_iff_of_iso (ringedOpenAdj l E j).unit
      (DerivedCategory.Q.objObjPreimageIso M)).mp (hQ _)
  exact NatIso.isIso_of_isIso_app _

private theorem derivedOpen_pull_counit_isIso {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback a j' j g)
    (K : Integral l E U) :
    IsIso ((ringedOpenAdj l E j').counit.app
      ((ringedPull l E g).obj ((ringedOpen l E j).obj K))) := by
  let J := PurCompactSupport.openExtension (PurCompactSupport.completed l E) j
  let G := integralOrdinaryPull l E g
  let B := PurCompactSupport.openExtension (PurCompactSupport.completed l E) j'
  let b := PurCompactSupport.openAdjunction (PurCompactSupport.completed l E) j'
  have hu := ordinaryOpen_unit_isIso l E j'
  have : B.Full := b.fullyFaithfulLOfIsIsoUnit.full
  have : B.Faithful := b.fullyFaithfulLOfIsIsoUnit.faithful
  have ho (M : scalarReductionSource l E U) : IsIso (b.counit.app (G.obj (J.obj M))) := by
    apply b.isIso_counit_app_iff_mem_essImage.mpr
    exact proEtaleRingPullback_openSupport a j' j g sq
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).ring U)
      ((PurCompactSupport.completed l E).ring X')
      ((PurCompactSupport.completed l E).ring U')
      ((PurCompactSupport.completed l E).pull j)
      ((PurCompactSupport.completed l E).pull g)
      ((PurCompactSupport.completed l E).pull j') M
  have hQ (P : CochainComplex (scalarReductionSource l E U) ℤ) :
      IsIso ((ringedOpenAdj l E j').counit.app
        ((ringedPull l E g).obj ((ringedOpen l E j).obj (DerivedCategory.Q.obj P)))) := by
    let T := (G.mapHomologicalComplex (.up ℤ)).obj
      ((J.mapHomologicalComplex (.up ℤ)).obj P)
    have hi (n : ℤ) : IsIso (((b.mapHomologicalComplex (.up ℤ)).counit.app T).f n) :=
      ho (P.X n)
    have := HomologicalComplex.Hom.isIso_of_components
      ((b.mapHomologicalComplex (.up ℤ)).counit.app T)
    have hc : IsIso ((ringedOpenAdj l E j').counit.app (DerivedCategory.Q.obj T)) := by
      simp only [ringedOpenAdj, PurCompactSupport.openDerivedAdjunction,
        Adjunction.localization_counit_app]
      infer_instance
    let e : (ringedPull l E g).obj ((ringedOpen l E j).obj (DerivedCategory.Q.obj P)) ≅
        DerivedCategory.Q.obj T :=
      G.mapDerivedCategory.mapIso (J.mapDerivedCategoryFactors.app P) ≪≫
        G.mapDerivedCategoryFactors.app ((J.mapHomologicalComplex (.up ℤ)).obj P)
    exact (NatTrans.isIso_app_iff_of_iso (ringedOpenAdj l E j').counit e).mpr hc
  let e := (ringedOpen l E j ⋙ ringedPull l E g).mapIso
    (DerivedCategory.Q.objObjPreimageIso K)
  exact (NatTrans.isIso_app_iff_of_iso (ringedOpenAdj l E j').counit e).mp (hQ _)

/-- The reverse open exchange, constructed from the actual open unit.
Source: Stacks 09AE (blueprint: lem-sf-integral-ringed-open-base-change). -/
def integralRingedOpenMate {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g) :
    ringedPull l E a ⋙ ringedOpen l E j' ⟶ ringedOpen l E j ⋙ ringedPull l E g where
  app M := ((ringedOpenAdj l E j').homEquiv _ _).symm
    ((ringedPull l E a).map ((ringedOpenAdj l E j).unit.app M) ≫
      (ringedSquare l E a j' j g h).inv.app ((ringedOpen l E j).obj M))
  naturality {M N} f := by
    apply ((ringedOpenAdj l E j').homEquiv _ _).injective
    simp only [Functor.comp_map]
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    simp only [Equiv.apply_symm_apply]
    have hn : f ≫ (ringedOpenAdj l E j).unit.app N =
        (ringedOpenAdj l E j).unit.app M ≫
          (ringedPull l E j).map ((ringedOpen l E j).map f) := by
      simpa only [Functor.id_map, Functor.comp_map] using
        (ringedOpenAdj l E j).unit.naturality f
    rw [← Category.assoc, ← (ringedPull l E a).map_comp, hn,
      (ringedPull l E a).map_comp]
    simp only [Category.assoc]
    congr 1
    simpa only [Functor.comp_map] using
      (ringedSquare l E a j' j g h).inv.naturality ((ringedOpen l E j).map f)

/-- For a cartesian open square the specified reverse mate is invertible.
Source: Stacks 03DI, 09AE; fix-prop-coherence, open base-change step
(blueprint: lem-sf-integral-ringed-open-base-change).

Proof: the open objects are subterminal, so their slice-extension units are
invertible. The open-slice presentations give full faithfulness, and hence
invertibility of the actual ordinary open units. Ordinary support preservation
places pullback of an extension in the essential image of the other open
extension, making its actual counit invertible. The termwise unit and counit are
isomorphisms on cochain complexes. The published localization formulas and the
standard factorization isomorphisms give the same statements on unbounded
derived categories; essential surjectivity of the localization covers every
object. Finally the inverse transpose defining integralRingedOpenMate is open
extension of an isomorphism followed by this invertible counit. Thus each of its
components is invertible. No additional normalization of ringedSquare is needed;
its inverse is an isomorphism by construction. -/
theorem integralRingedOpenMate_isIso {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (_sq : IsPullback a j' j g) :
    IsIso (integralRingedOpenMate l E a j' j g h) := by
  have hu := derivedOpen_unit_isIso l E j
  have hc := derivedOpen_pull_counit_isIso l E a j' j g _sq
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  change IsIso (((ringedOpenAdj l E j').homEquiv _ _).symm
    ((ringedPull l E a).map ((ringedOpenAdj l E j).unit.app M) ≫
      (ringedSquare l E a j' j g h).inv.app ((ringedOpen l E j).obj M)))
  rw [Adjunction.homEquiv_counit]
  infer_instance

end WeilConjectures.IntegralSystemRealization
