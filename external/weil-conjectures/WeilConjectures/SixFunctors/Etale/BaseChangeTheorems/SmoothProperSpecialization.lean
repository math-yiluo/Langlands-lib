/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselianLift
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.ClosedOpen
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.StrictlyHenselianUnit
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.SixFunctors.OpenClosed.Conservative

/-!
# The specialization isomorphism for smooth proper morphisms over a strictly local base

Let `R` be a strictly henselian local ring with closed point `s₀ : Spec κ ⟶ Spec R`, let
`π : X ⟶ Spec R` be smooth, `t : Spec Ω ⟶ Spec R` a geometric point (`Ω` separably closed)
and

```
X_t --h--> X
 |         |
π_t        π
 v         v
Spec Ω -t-> Spec R
```

the base change. Let `Λ` be a coefficient ring killed by an integer `N ≠ 0` invertible in `R`
and `F` a locally constant sheaf of `Λ`-modules on `X_ét`. This file proves Step 1 of the
blueprint proof of `theorem-purity-higher-direct-images-under` (the specialization isomorphism):

- **local acyclicity along the closed fibre**: for every morphism `i : Z ⟶ X` landing in the
  closed fibre, `i^*(F ⟶ Rh_* h^* F)` is an isomorphism
  (`AlgebraicGeometry.Etale.isIso_upperStar_map_unit_of_smooth`). Étale locally on `X` the
  sheaf `F` is constant; by smooth base change (`theorem-smooth-base-change-classical-torsion--1`)
  along `U ⟶ Spec R` and `t`, `Rh_{U*} M ≅ (U → Spec R)^* Rt_* M`, and the stalk at the closed point
  of `M ⟶ Rt_* t^* M` is an isomorphism since `Spec R` is strictly local and `Ω` is separably
  closed
  (`Etale.isIso_upperStar_map_unit_constantSheaf_of_isStrictlyHenselianLocalRing`).
- **the specialization isomorphism**: if moreover `π` is proper, the closed stalk of
  `Rπ_* F ⟶ Rπ_* Rh_* h^* F` is an isomorphism
  (`AlgebraicGeometry.Etale.isIso_upperStar_map_lowerStar_map_unit_of_smooth_of_isProper`): by
  proper base change for the closed fibre `X_s` it is `Rπ_{s*}` of the restriction to `X_s` of
  `F ⟶ Rh_* h^* F`.

Since `Spec R` is strictly local, the closed stalk of `Rπ_* K` is `RΓ(X, K)`, and
`Rπ_* Rh_* = Rt_* Rπ_{t*}`; thus the second statement says that the restriction
`Hᵠ(X, F) ⟶ Hᵠ(X_t, h^* F)` is bijective.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- A ring killed by a nonzero integer is torsion as an additive group. -/
lemma isAddTorsion_of_natCast_eq_zero {S : Type*} [Ring S] (N : ℕ) (hN₀ : N ≠ 0)
    (hN : (N : S) = 0) : IsAddTorsion S := fun x ↦
  isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨N, Nat.pos_of_ne_zero hN₀, by
    rw [nsmul_eq_mul, hN, zero_mul]⟩

/-- In a commutative square `a ≫ b = c ≫ d` whose right-hand legs `b` and `d` are isomorphisms,
`a` is an isomorphism if and only if `c` is. -/
lemma _root_.CategoryTheory.isIso_iff_of_comp_eq_comp_of_isIso_right {C : Type*} [Category* C]
    {W X Y Z : C} {a : W ⟶ X} {b : X ⟶ Z} {c : W ⟶ Y} {d : Y ⟶ Z} {e : W ⟶ Z}
    [IsIso b] [IsIso d] (h₁ : e = a ≫ b) (h₂ : e = c ≫ d) : IsIso a ↔ IsIso c := by
  constructor
  · intro
    have : IsIso (c ≫ d) := by
      rw [← h₂, h₁]
      infer_instance
    exact IsIso.of_isIso_comp_right c d
  · intro
    have : IsIso (a ≫ b) := by
      rw [← h₁, h₂]
      infer_instance
    exact IsIso.of_isIso_comp_right a b

/-- **Units across a base-change isomorphism.** For a commutative square `sq` whose base-change
morphism is an isomorphism at `f^* L`, a functor `Φ` out of `D⁺(Y'_ét)` sends the pullback along
`g` of the unit `L ⟶ Rf_* f^* L` to an isomorphism if and only if it sends the unit
`g^* L ⟶ Rf'_* f'^* g^* L` to an isomorphism
(`AlgebraicGeometry.Etale.upperStar_map_unit_comp_baseChange_app`). -/
lemma Etale.isIso_map_upperStar_map_unit_iff {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} {C : Type*} [Category* C]
    (Φ : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤ C)
    (sq : CommSq g' f' f g)
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app
      (D+((f)^*[ModuleCat.{u + 1} Λ]).obj L))] :
    IsIso (Φ.map (D+((g)^*[ModuleCat.{u + 1} Λ]).map
        ((derivedUpperStarLowerStarAdjunctionPlus _ f).unit.app L))) ↔
      IsIso (Φ.map ((derivedUpperStarLowerStarAdjunctionPlus _ f').unit.app
        (D+((g)^*[ModuleCat.{u + 1} Λ]).obj L))) := by
  exact isIso_iff_of_comp_eq_comp_of_isIso_right (Φ.map_comp _ _)
    ((congrArg Φ.map
      (Etale.upperStar_map_unit_comp_baseChange_app Λ sq L)).trans (Φ.map_comp _ _))

/-- **Pullbacks along a jointly surjective family are conservative on `D⁺`.** A morphism `φ` of
`D⁺(X_ét)` is an isomorphism as soon as its pullbacks along a jointly surjective family of
morphisms `a i : U i ⟶ X` are. -/
lemma Etale.isIso_of_isIso_mapDerivedCategoryPlus_upperStar_map_of_jointlySurjective
    {X : Scheme.{u}} {ι : Type u} {U : ι → Scheme.{u}} (a : ∀ i, U i ⟶ X)
    (ha : ∀ x : X, ∃ (i : ι) (y : U i), (a i).base y = x)
    {K L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (φ : K ⟶ L)
    (hφ : ∀ i, IsIso (D+((a i)^*[ModuleCat.{u + 1} Λ]).map φ)) : IsIso φ := by
  rw [DerivedCategory.Plus.isIso_iff]
  intro q
  refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective _ a ha _ fun i ↦ ?_
  rw [← Functor.comp_map, NatIso.isIso_map_iff
    (((a i)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso q), Functor.comp_map]
  infer_instance

variable {R : Type u} [CommRing R] [IsStrictlyHenselianLocalRing R]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] {t : Spec (.of Ω) ⟶ Spec (.of R)}

/-- **Local acyclicity for a constant sheaf.** Let `e : U ⟶ Spec R` be smooth over a strictly
henselian local ring, `t : Spec Ω ⟶ Spec R` a geometric point with base change
`h_U : U_t ⟶ U`, and `M` a module over a coefficient ring killed by an integer `N ≠ 0`
invertible in `R`. For every `v : V ⟶ U` landing over the closed point of `Spec R`,
`v^*(e^* M ⟶ Rh_{U*} h_U^* e^* M)` is an isomorphism.

By smooth base change (`theorem-smooth-base-change-classical-torsion--1`) the unit of `h_U` at
`e^* M` is the pullback along `e` of the unit `M ⟶ Rt_* t^* M`, whose restriction to the closed
point is an isomorphism
(`Etale.isIso_upperStar_map_unit_constantSheaf_of_isStrictlyHenselianLocalRing`).
-/
theorem Etale.isIso_upperStar_map_unit_upperStar_constantSheaf_of_smooth
    {U Ut V : Scheme.{u}} (e : U ⟶ Spec (.of R)) [Smooth e] {et : Ut ⟶ Spec (.of Ω)}
    {hU : Ut ⟶ U} (sq : IsPullback et hU t e) (N : ℕ) (hN₀ : N ≠ 0) (hN : (N : Λ) = 0)
    (hNR : IsUnit (N : Γ(Spec (.of R), ⊤))) (v : V ⟶ U)
    (w : V ⟶ Spec (.of (IsLocalRing.ResidueField R)))
    (hvw : v ≫ e = w ≫ closedGeometricPoint R)
    (M : ModuleCat.{u + 1} Λ) :
    IsIso (D+((v)^*[ModuleCat.{u + 1} Λ]).map
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) hU).unit.app
        (D+((e)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((constantSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))))) := by
  have : IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
      (D+((t)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((constantSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) :=
    Etale.isIso_baseChange_app_of_smooth_of_isTorsionSheafOfInvertibleOrder Λ e sq _ fun _ ↦
      IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero Λ N hN₀ hN hNR _
  rw [← Etale.isIso_map_upperStar_map_unit_iff Λ _ sq.toCommSq,
    ← Functor.comp_map, NatIso.isIso_map_iff
      ((Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) v e).symm ≪≫
        eqToIso (by rw [hvw]) ≪≫
        Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) w (closedGeometricPoint R)),
    Functor.comp_map]
  have := Etale.isIso_upperStar_map_unit_constantSheaf_of_isStrictlyHenselianLocalRing Λ R t M
  infer_instance

/-- A functor `Φ` sends the component of a natural transformation `α` at `K` to an isomorphism
if and only if it does so at any object isomorphic to `K`. -/
lemma _root_.CategoryTheory.NatTrans.isIso_map_app_iff_of_iso {C D E : Type*} [Category* C]
    [Category* D] [Category* E] {F G : C ⥤ D} (α : F ⟶ G) (Φ : D ⥤ E)
    {K K' : C} (e : K ≅ K') :
    IsIso (Φ.map (α.app K)) ↔ IsIso (Φ.map (α.app K')) :=
  NatTrans.isIso_app_iff_of_iso (Functor.whiskerRight α Φ) e

/-- **Local acyclicity along the closed fibre** (Step 1 of the blueprint proof of
`theorem-purity-higher-direct-images-under`). Let `π : X ⟶ Spec R` be smooth over a
strictly henselian local ring, `t : Spec Ω ⟶ Spec R` a geometric point with base change
`h : X_t ⟶ X`, and `F` a locally constant sheaf of modules over a coefficient ring killed by
an integer `N ≠ 0`
invertible in `R`. For every morphism `i : Z ⟶ X` landing in the closed fibre (for instance the
closed fibre itself), `i^*(F ⟶ Rh_* h^* F)` is an isomorphism in `D⁺(Z_ét)`.

The question is local on a trivialising étale cover `U_j ⟶ X` of `F`; by étale (smooth) base
change the unit of `h` restricts on `U_j` to the unit of `h_{U_j} : U_j ×_X X_t ⟶ U_j` at the
constant sheaf, where
`AlgebraicGeometry.Etale.isIso_upperStar_map_unit_upperStar_constantSheaf_of_smooth` applies. -/
theorem Etale.isIso_upperStar_map_unit_of_smooth {X Xt Z : Scheme.{u}} (π : X ⟶ Spec (.of R))
    [Smooth π] {πt : Xt ⟶ Spec (.of Ω)} {h : Xt ⟶ X} (sq : IsPullback πt h t π) (N : ℕ)
    (hN₀ : N ≠ 0) (hN : (N : Λ) = 0) (hNR : IsUnit (N : Γ(Spec (.of R), ⊤))) (i : Z ⟶ X)
    (πs : Z ⟶ Spec (.of (IsLocalRing.ResidueField R)))
    (hi : i ≫ π = πs ≫ closedGeometricPoint R)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsLocallyConstantSheaf F] :
    IsIso (D+((i)^*[ModuleCat.{u + 1} Λ]).map
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h).unit.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
  have hqc : QuasiCompact h := MorphismProperty.of_isPullback sq inferInstance
  have hqs : QuasiSeparated h := MorphismProperty.of_isPullback sq inferInstance
  have hNX : IsUnit (N : Γ(X, ⊤)) := by simpa using hNR.map π.appTop.hom
  refine Etale.isIso_of_isIso_mapDerivedCategoryPlus_upperStar_map_of_jointlySurjective Λ
    (fun j ↦ pullback.snd (𝒰.f j) i) (fun z ↦ ?_) _ fun j ↦ ?_
  · obtain ⟨j, x, hx⟩ := 𝒰.exists_eq (i z)
    obtain ⟨y, -, hy⟩ := Scheme.Pullback.exists_preimage_pullback x z hx
    exact ⟨j, y, hy⟩
  -- the pullback to `V_j = U_j ×_X Z` factors through `U_j`
  rw [← Functor.comp_map, NatIso.isIso_map_iff
    ((Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) (pullback.snd (𝒰.f j) i) i).symm ≪≫
      eqToIso (by rw [pullback.condition]) ≪≫
      Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) (pullback.fst (𝒰.f j) i) (𝒰.f j)),
    Functor.comp_map]
  -- étale base change along `U_j ⟶ X`
  have hBC : IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ)
      (IsPullback.of_hasPullback h (𝒰.f j)).toCommSq).app
        (D+((h)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) :=
    Etale.isIso_baseChange_app_of_smooth_of_isTorsionSheafOfInvertibleOrder Λ (𝒰.f j)
      (IsPullback.of_hasPullback h (𝒰.f j)) _ fun _ ↦
        IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero Λ N hN₀ hN hNX _
  rw [Etale.isIso_map_upperStar_map_unit_iff Λ _
    (IsPullback.of_hasPullback h (𝒰.f j)).toCommSq]
  -- `F` is constant on `U_j`
  have hc : ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f j)).obj F).IsConstant
      (𝒰.X j).smallEtaleTopology :=
    (isConstant_over_iff_upperStar _ (𝒰.etalePrecoverageToEtale j) F).mp (h𝒰 j)
  obtain ⟨M, ⟨eM⟩⟩ := Sheaf.mem_essImage_of_isConstant _
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f j)).obj F)
  let eK : D+((𝒰.f j ≫ π)^*[ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((constantSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) ≅
      D+((𝒰.f j)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F) :=
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f j ≫ π)).mapDerivedCategoryPlusSingleFunctor
        0).app _ ≪≫
      (DerivedCategory.Plus.singleFunctor _ 0).mapIso
        ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) (𝒰.f j ≫ π)).app M ≪≫
          eM) ≪≫
      (((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f j)).mapDerivedCategoryPlusSingleFunctor
        0).app F).symm
  rw [← NatTrans.isIso_map_app_iff_of_iso _ _ eK]
  refine Etale.isIso_upperStar_map_unit_upperStar_constantSheaf_of_smooth Λ (𝒰.f j ≫ π)
    ((IsPullback.of_hasPullback h (𝒰.f j)).paste_horiz sq) N hN₀ hN hNR _
    (pullback.snd (𝒰.f j) i ≫ πs) ?_ M
  rw [reassoc_of% pullback.condition, hi, Category.assoc]

/-- **The specialization isomorphism over a strictly local base** (Step 1 of the blueprint proof
of `theorem-purity-higher-direct-images-under`). Let `π : X ⟶ Spec R` be smooth and proper over a
strictly henselian local ring, with closed fibre `i : X_s ⟶ X`, let `t : Spec Ω ⟶ Spec R` be a
geometric point with base change `h : X_t ⟶ X`, and let `F` be a locally constant sheaf of
modules over a coefficient ring killed by an integer `N ≠ 0` invertible in `R`. Then the
restriction to the closed point of `Rπ_* F ⟶ Rπ_* Rh_* h^* F` is an isomorphism.

By proper base change (`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring`)
for the closed fibre, this map is `Rπ_{s*}` of `i^*(F ⟶ Rh_* h^* F)`, an isomorphism by
`AlgebraicGeometry.Etale.isIso_upperStar_map_unit_of_smooth`. As `Spec R` is strictly local, the
closed stalk of `Rπ_* K` is `RΓ(X, K)` and `Rπ_* Rh_* = Rt_* Rπ_{t*}`, so this says that the
restriction `Hᵠ(X, F) ⟶ Hᵠ(X_t, h^* F)` is bijective for every `q`. -/
theorem Etale.isIso_upperStar_map_lowerStar_map_unit_of_smooth_of_isProper
    {X Xt Xs : Scheme.{u}} (π : X ⟶ Spec (.of R)) [Smooth π] [IsProper π]
    {πt : Xt ⟶ Spec (.of Ω)} {h : Xt ⟶ X} (sq : IsPullback πt h t π) (N : ℕ)
    (hN₀ : N ≠ 0) (hN : (N : Λ) = 0) (hNR : IsUnit (N : Γ(Spec (.of R), ⊤))) {i : Xs ⟶ X}
    {πs : Xs ⟶ Spec (.of (IsLocalRing.ResidueField R))}
    (sqs : IsPullback i πs π (closedGeometricPoint R))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsLocallyConstantSheaf F] :
    IsIso (D+((closedGeometricPoint R)^*[ModuleCat.{u + 1} Λ]).map
      (R+((π)_*[ModuleCat.{u + 1} Λ]).map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h).unit.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) := by
  have := Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring Λ
    (isAddTorsion_of_natCast_eq_zero N hN₀ hN) sqs
  have := Etale.isIso_upperStar_map_unit_of_smooth Λ π sq N hN₀ hN hNR i πs sqs.w F
  have hnat := (Etale.baseChange (ModuleCat.{u + 1} Λ) sqs.toCommSq).naturality
    ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h).unit.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
  have : IsIso ((R+((π)_*[ModuleCat.{u + 1} Λ]) ⋙
      D+((closedGeometricPoint R)^*[ModuleCat.{u + 1} Λ])).map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h).unit.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
      (Etale.baseChange (ModuleCat.{u + 1} Λ) sqs.toCommSq).app _) := by
    rw [hnat]
    exact IsIso.comp_isIso' inferInstance (Functor.map_isIso (R+((πs)_*[ModuleCat.{u + 1} Λ])) _)
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _
    ((Etale.baseChange (ModuleCat.{u + 1} Λ) sqs.toCommSq).app _) inferInstance this

/-- **The specialization isomorphism, transition form.** Under the hypotheses of
`AlgebraicGeometry.Etale.isIso_upperStar_map_lowerStar_map_unit_of_smooth_of_isProper`, for any
`h'` with `h ≫ π = h'` (e.g. `h' = π_t ≫ t`), the restriction to the closed point of the
transition map `Rπ_* F ⟶ Rh'_* h^* F` (`AlgebraicGeometry.Etale.lowerStarPlusTransition`) is an
isomorphism. For `h' = π_t ≫ t` the target is `Rt_* Rπ_{t*} h^* F`, whose closed stalk is
`RΓ(X_t, h^* F)`. -/
theorem Etale.isIso_upperStar_map_lowerStarPlusTransition_of_smooth_of_isProper
    {X Xt Xs : Scheme.{u}} (π : X ⟶ Spec (.of R)) [Smooth π] [IsProper π]
    {πt : Xt ⟶ Spec (.of Ω)} {h : Xt ⟶ X} (sq : IsPullback πt h t π) (N : ℕ)
    (hN₀ : N ≠ 0) (hN : (N : Λ) = 0) (hNR : IsUnit (N : Γ(Spec (.of R), ⊤))) {i : Xs ⟶ X}
    {πs : Xs ⟶ Spec (.of (IsLocalRing.ResidueField R))}
    (sqs : IsPullback i πs π (closedGeometricPoint R)) (h' : Xt ⟶ Spec (.of R))
    (w : h ≫ π = h') (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsLocallyConstantSheaf F] :
    IsIso (D+((closedGeometricPoint R)^*[ModuleCat.{u + 1} Λ]).map
      (Etale.lowerStarPlusTransition Λ h π h' w
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  have hc := Etale.lowerStarPlusTransition_comp_map Λ h π h' w
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F) _ (𝟙 _)
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at hc
  rw [hc]
  erw [Category.comp_id]
  rw [Functor.map_comp]
  have := Etale.isIso_upperStar_map_lowerStar_map_unit_of_smooth_of_isProper Λ π sq N hN₀ hN
    hNR sqs F
  infer_instance

end AlgebraicGeometry
