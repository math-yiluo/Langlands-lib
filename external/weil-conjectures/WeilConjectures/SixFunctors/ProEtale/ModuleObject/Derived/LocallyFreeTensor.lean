/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.ModuleObjects.FreeMap
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeConstructible

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeDualizable
import WeilConjectures.TraceFormula.CategoricalTraceBiproduct

/-!
# Tensor products with locally free module objects

Let `Λ` be a commutative condensed ring and `X` a scheme. For a locally free module object `P`
over `Λ_X` (`ProEtale.IsLocallyFree`):

* the pullback `g^* P` along any morphism `g` is locally free
  (`ProEtale.IsLocallyFree.upperStar`);
* `P ⊗ N` is pro-étale locally finitely presented, resp. constructible, if `N` is
  (`ProEtale.IsLocallyFree.isLocallyFinitelyPresented_tensorObj`,
  `ProEtale.IsLocallyFree.isConstructibleModuleObject_tensorObj`);
* `P` is flat, so the derived tensor product `P[0] ⊗ᴸ N[n]` is `(P ⊗ N)[n]`
  (`ProEtale.IsLocallyFree.singleFunctorTensorObjIso`);
* `P[q]` is dualizable in `D(Mod_{Λ_X})`, with dual `P'[-q]` for a locally free `P'`
  (`ProEtale.IsLocallyFree.exists_exactPairing_singleFunctor`).

This file does not import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, so that the
latter can use these statements.
-/

public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

/-! ### Pullbacks of free module objects -/

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- Freeness of the pullback `f^* N` of a module object can be read either over `f^* Λ_X` or over
`Λ_W`, the two being identified by the isomorphism of ring objects `α_f : f^* Λ_X ⟶ Λ_W`. -/
lemma isFree_mapMod_iff {W X : Scheme.{u}} (f : W ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Mod.IsFree ((f)^*[Ab.{u + 1}].obj (condensedRingObj Λ X))
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)).obj N) ↔
      Mod.IsFree (condensedRingObj Λ W) ((f)^*⟦Λ⟧.obj N) := by
  let α := condensedPullbackHom Λ f
  refine ⟨fun h ↦ (h.comap (asIso α).inv).of_iso ?_, fun h ↦ (h.comap α).of_iso ?_⟩
  · exact ((Mod.extendScalarsIsoComapInv α).app _).symm
  · exact comapUpperStarObjIso Λ f N

/-- The pullback of module objects over `Λ` preserves free module objects of finite rank. -/
lemma IsFree.upperStar {W Y : Scheme.{u}} (g : W ⟶ Y)
    {N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
    (hN : Mod.IsFree (condensedRingObj Λ Y) N) :
    Mod.IsFree (condensedRingObj Λ W) ((g)^*⟦Λ⟧.obj N) :=
  hN.map _ (upperStarObjRegularIso Λ g)

/-- Along a commutative square `a ≫ f = b ≫ g`, if `f^* M` is free, then so is
`b^* g^* M ≅ a^* f^* M`. -/
lemma isFree_upperStar_upperStar_of_comm {P U W X : Scheme.{u}} {a : P ⟶ U}
    {b : P ⟶ W} {f : U ⟶ X} {g : W ⟶ X} (h : a ≫ f = b ≫ g)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : Mod.IsFree (condensedRingObj Λ U) ((f)^*⟦Λ⟧.obj M)) :
    Mod.IsFree (condensedRingObj Λ P) ((b)^*⟦Λ⟧.obj ((g)^*⟦Λ⟧.obj M)) :=
  (IsFree.upperStar Λ a hM).of_iso (upperStarSquareIso Λ h M)

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

/-! ### Local freeness and duals -/

/-- A right dual of a free module object of finite rank over a commutative ring object of
pro-étale sheaves is free: it is isomorphic to the self-dual `Sⁿ`. -/
lemma isFree_of_exactPairing {W : Scheme.{u}} {S : Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}}
    [MonObj S] [IsCommMonObj S] {M D : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) S}
    [ExactPairing M D] (hM : Mod.IsFree S M) : Mod.IsFree S D := by
  obtain ⟨n, ⟨e⟩⟩ := hM
  let p : ExactPairing (⨁ fun _ : Fin n ↦ 𝟙_ (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) S))
      (⨁ fun _ : Fin n ↦ 𝟙_ (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) S)) :=
    Bicone.exactPairing (biproduct.isBilimit _) (biproduct.isBilimit _)
  exact ⟨n, ⟨rightDualIso (exactPairingCongrLeft e.symm) p⟩⟩

/-- A right dual of a locally free module object is locally free: the restrictions to the
members of a cover are strong monoidal, hence preserve exact pairings. -/
lemma IsLocallyFree.of_exactPairing {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {M D : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R} [ExactPairing M D]
    (hM : IsLocallyFree R M) : IsLocallyFree R D := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  refine ⟨𝒰, fun i ↦ ?_⟩
  let _ := ExactPairing.map ((𝒰.f i)^*[Ab.{u + 1}].mapMod R) M D
  exact isFree_of_exactPairing (h𝒰 i)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

variable {Λ} in
/-- Local freeness over `Λ_X` read with the pullbacks of module objects over `Λ`. -/
lemma isLocallyFree_iff {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsLocallyFree (condensedRingObj Λ X) M ↔
      ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X,
        ∀ i : 𝒰.I₀, Mod.IsFree (condensedRingObj Λ (𝒰.X i)) ((𝒰.f i)^*⟦Λ⟧.obj M) :=
  exists_congr fun _ ↦ forall_congr' fun _ ↦ isFree_mapMod_iff Λ _ M

variable {Λ} in
/-- Pro-étale local finite presentation over `Λ_X` read with the pullbacks of module objects
over `Λ`. -/
lemma isLocallyFinitelyPresented_iff {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X) M ↔
      ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X,
        ∀ i : 𝒰.I₀,
          Mod.IsFinitelyPresented (condensedRingObj Λ (𝒰.X i)) ((𝒰.f i)^*⟦Λ⟧.obj M) :=
  exists_congr fun _ ↦ forall_congr' fun _ ↦ isFinitelyPresented_mapMod_iff Λ _ M

variable {Λ} in
/-- A free module object of finite rank is locally free, for the trivial cover. -/
lemma isLocallyFree_of_isFree {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : Mod.IsFree (condensedRingObj Λ X) M) : IsLocallyFree (condensedRingObj Λ X) M :=
  ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _),
    fun _ ↦ (isFree_mapMod_iff Λ _ _).2 (IsFree.upperStar Λ _ hM)⟩

variable {Λ} in
/-- Pro-étale local finite presentation is local: if the pullbacks of `M` to the members of a
pro-étale cover are locally finitely presented, so is `M`. -/
lemma isLocallyFinitelyPresented_of_cover {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (h : ∀ i, IsLocallyFinitelyPresented (condensedRingObj Λ (𝒰.X i)) ((𝒰.f i)^*⟦Λ⟧.obj M)) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X) M := by
  choose 𝒱 h𝒱 using h
  refine ⟨𝒰.bind 𝒱, fun i ↦ ?_⟩
  obtain ⟨i, j⟩ := i
  have h₁ : Mod.IsFinitelyPresented (condensedRingObj Λ ((𝒱 i).X j))
      (((𝒱 i).f j ≫ 𝒰.f i)^*⟦Λ⟧.obj M) :=
    ((isFinitelyPresented_mapMod_iff Λ _ _).1 (h𝒱 i j)).of_iso
      ((CondensedRing.upperStarComp Λ ((𝒱 i).f j) (𝒰.f i)).app M).symm
  exact (isFinitelyPresented_mapMod_iff Λ ((𝒱 i).f j ≫ 𝒰.f i) M).2 h₁

variable {Λ} in
/-- The tensor product of a free module object of finite rank and a finitely presented one is
finitely presented. -/
lemma isFinitelyPresented_tensorObj_of_isFree {X : Scheme.{u}}
    {P N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hP : Mod.IsFree (condensedRingObj Λ X) P)
    (hN : Mod.IsFinitelyPresented (condensedRingObj Λ X) N) :
    Mod.IsFinitelyPresented (condensedRingObj Λ X) (P ⊗ N) :=
  have hP' : Mod.IsFree (condensedRingObj Λ X) ((tensorLeft P).obj (Mod.regular _)) :=
    hP.of_iso (ρ_ P).symm
  hN.map_of_isFree (tensorLeft P) hP'

variable {Λ} in
/-- The tensor product of a free module object of finite rank and a pro-étale locally finitely
presented one is pro-étale locally finitely presented. -/
lemma isLocallyFinitelyPresented_tensorObj_of_isFree {X : Scheme.{u}}
    {P N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hP : Mod.IsFree (condensedRingObj Λ X) P)
    (hN : IsLocallyFinitelyPresented (condensedRingObj Λ X) N) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X) (P ⊗ N) := by
  obtain ⟨𝒱, h𝒱⟩ := (isLocallyFinitelyPresented_iff N).1 hN
  exact (isLocallyFinitelyPresented_iff _).2 ⟨𝒱, fun j ↦
    (isFinitelyPresented_tensorObj_of_isFree (IsFree.upperStar Λ _ hP) (h𝒱 j)).of_iso
      (Functor.Monoidal.μIso ((𝒱.f j)^*⟦Λ⟧) P N)⟩

/-! ### Main statements -/

/-- The pullback `g^*` of module objects over `Λ` preserves local freeness. -/
lemma IsLocallyFree.upperStar {W X : Scheme.{u}} (g : W ⟶ X)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsLocallyFree (condensedRingObj Λ X) M) :
    IsLocallyFree (condensedRingObj Λ W) ((g)^*⟦Λ⟧.obj M) := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  refine ⟨𝒰.pullback₁ g, fun i ↦ ?_⟩
  let a : (𝒰.pullback₁ g).X i ⟶ 𝒰.X i := pullback.snd g (𝒰.f i)
  exact (isFree_mapMod_iff Λ _ _).2
    (isFree_upperStar_upperStar_of_comm Λ (a := a) (b := (𝒰.pullback₁ g).f i)
      pullback.condition.symm ((isFree_mapMod_iff Λ _ _).1 (h𝒰 i)))

variable {Λ} in
/-- The tensor product of a locally free and a pro-étale locally finitely presented module object
is pro-étale locally finitely presented. -/
lemma IsLocallyFree.isLocallyFinitelyPresented_tensorObj {X : Scheme.{u}}
    {P N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hP : IsLocallyFree (condensedRingObj Λ X) P)
    (hN : IsLocallyFinitelyPresented (condensedRingObj Λ X) N) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X) (P ⊗ N) := by
  obtain ⟨𝒰, h𝒰⟩ := (isLocallyFree_iff P).1 hP
  exact isLocallyFinitelyPresented_of_cover 𝒰 fun i ↦
    (isLocallyFinitelyPresented_tensorObj_of_isFree (h𝒰 i)
      (IsLocallyFinitelyPresented.upperStar Λ _ hN)).of_iso
      (Functor.Monoidal.μIso ((𝒰.f i)^*⟦Λ⟧) P N)

variable {Λ} in
/-- The tensor product of a locally free and a constructible module object is constructible. -/
lemma IsLocallyFree.isConstructibleModuleObject_tensorObj {X : Scheme.{u}}
    {P N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hP : IsLocallyFree (condensedRingObj Λ X) P)
    (hN : IsConstructibleModuleObject (condensedRingObj Λ X) N) :
    IsConstructibleModuleObject (condensedRingObj Λ X) (P ⊗ N) := by
  obtain ⟨S, hS⟩ := hN
  refine ⟨S, fun a ↦ (isLocallyFinitelyPresented_mapMod_iff Λ _ _).2 ?_⟩
  exact (IsLocallyFree.isLocallyFinitelyPresented_tensorObj (hP.upperStar Λ _)
    ((isLocallyFinitelyPresented_mapMod_iff Λ _ _).1 (hS a))).of_iso
    (Functor.Monoidal.μIso ((S.immersion a)^*⟦Λ⟧) P N)

variable {Λ} in
/-- A locally free module object is flat: it is dualizable. -/
theorem IsLocallyFree.flat {X : Scheme.{u}}
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hP : IsLocallyFree (condensedRingObj Λ X) P) : ObjectProperty.flat P :=
  ObjectProperty.flat_of_isDualizable hP.isDualizable

variable {Λ} in
/-- A locally free module object `P` is flat, so the derived tensor product of `P[0]` and
`N[n]` is `(P ⊗ N)[n]`. -/
noncomputable def IsLocallyFree.singleFunctorTensorObjIso {X : Scheme.{u}}
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hP : IsLocallyFree (condensedRingObj Λ X) P)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) (n : ℤ) :
    (DerivedCategory.singleFunctor _ 0).obj P ⊗
        (DerivedCategory.singleFunctor _ n).obj N ≅
      (DerivedCategory.singleFunctor _ n).obj (P ⊗ N) :=
  tensorIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app P)
      ((DerivedCategory.singleFunctorIsoCompQ _ n).app N) ≪≫
    DerivedCategory.QObjTensorQObjIsoOfKFlatLeft _ _
      ((CochainComplex.kFlat_single_obj_iff_flat P 0).2 hP.flat) ≪≫
    DerivedCategory.Q.mapIso
      ((CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor _) P).app _ ≪≫
        (HomologicalComplex.singleMapHomologicalComplex (tensorLeft P) (.up ℤ) n).app N) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ n).app (P ⊗ N)).symm

variable {Λ} in
/-- A locally free module object `P` placed in degree `q` is dualizable in `D(Mod_{Λ_X})`: it has
a left dual `P'[-q]` with `P'` locally free. -/
lemma IsLocallyFree.exists_exactPairing_singleFunctor {X : Scheme.{u}}
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hP : IsLocallyFree (condensedRingObj Λ X) P) (q : ℤ) :
    ∃ P' : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
      IsLocallyFree (condensedRingObj Λ X) P' ∧
        Nonempty (ExactPairing ((DerivedCategory.singleFunctor _ (-q)).obj P')
          ((DerivedCategory.singleFunctor _ q).obj P)) := by
  let C := (HomologicalComplex.single
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (ComplexShape.up ℤ) q).obj P
  have hC (m : ℤ) : IsDualizable (C.X m) := by
    by_cases hm : m = q
    · subst hm
      exact hP.isDualizable.of_iso (HomologicalComplex.singleObjXSelf _ _ P).symm
    · exact CategoryTheory.IsZero.isDualizable (HomologicalComplex.isZero_single_obj_X _ _ _ _ hm)
  let _ (m : ℤ) : HasRightDual (C.X m) := (hC m).some
  obtain ⟨_⟩ := DerivedCategory.nonempty_exactPairing_Q_obj C q q
  obtain ⟨_⟩ := DerivedCategory.nonempty_braidedCategory
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  let _ := BraidedCategory.exactPairing_swap (DerivedCategory.Q.obj C)
    (DerivedCategory.Q.obj (CochainComplex.rightDual C))
  obtain ⟨M, ⟨eM⟩⟩ := CochainComplex.exists_iso_single (CochainComplex.rightDual C) (-q)
  have h₁ : IsLocallyFree (condensedRingObj Λ X) (C.X (-(-q))) :=
    hP.of_iso (HomologicalComplex.singleObjXIsoOfEq _ q P (-(-q)) (neg_neg q)).symm
  refine ⟨M, (IsLocallyFree.of_exactPairing (D := (C.X (-(-q)))ᘁ) h₁).of_iso ?_, ⟨?_⟩⟩
  · exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) (-q)).mapIso eM ≪≫
      HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-q) M
  · exact exactPairingCongr (X' := DerivedCategory.Q.obj (CochainComplex.rightDual C))
      (Y' := DerivedCategory.Q.obj C)
      ((DerivedCategory.singleFunctorIsoCompQ _ (-q)).app M ≪≫ DerivedCategory.Q.mapIso eM.symm)
      ((DerivedCategory.singleFunctorIsoCompQ _ q).app P)

/-- The unit `Λ_X` of the module objects over `Λ_X` is locally free (indeed free of rank one). -/
lemma isLocallyFree_tensorUnit (X : Scheme.{u}) :
    IsLocallyFree (condensedRingObj Λ X)
      (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
  isLocallyFree_of_isFree
    ⟨1, ⟨(biproductUniqueIso (fun _ : Fin 1 ↦ Mod.regular (condensedRingObj Λ X))).symm⟩⟩

end AlgebraicGeometry.ProEtale
