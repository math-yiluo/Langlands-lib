/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.TraceFormula.Additivity
public import WeilConjectures.TraceFormula.ShriekTraceFunction
public import WeilConjectures.TraceFormula.WeilDistTriangLowerShriek
public import WeilConjectures.TraceFormula.WeilDistTriangTrace
public import WeilConjectures.TraceFormula.WeilSheafUpperStar
public import WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar

/-!

# Dévissage of the sheaf–function compatibility along an open–closed decomposition

Let `f : X ⟶ Y` be a morphism with automorphisms `e_X`, `e_Y`, and let `j : U ⟶ X` be an open
immersion with closed complement `i : Z ⟶ X`, both stable under `e_X`. The sheaf–function
compatibility (`ProEtale.CondensedRing.ShriekTraceFunctionAt`) along `j ≫ f` and along `i ≫ f`
gives it along `f` (`ProEtale.CondensedRing.shriekTraceFunctionAt_of_isCompl`).

The proof splits the points of `X` over `ȳ` into those of `U` and those of `Z`, and uses two
inputs, stated here as separate lemmas:

- `ProEtale.CondensedRing.weilStalkTraceAlternatingSum_weilLowerShriek_eq_add`: the local trace of
  `Rf_!^Weil K` is the sum of those of `R(j ≫ f)_!^Weil j^* K` and `R(i ≫ f)_!^Weil i^* K`. It
  comes from the localization triangle `j_! j^* K ⟶ K ⟶ i_* i^* K ⟶` of Weil objects, the
  compatibility of the Frobenius with its connecting morphism (blueprint
  `lemma-additivity-open-subscheme-complement`, Step 2) and the additivity of the supertrace along
  the long exact sequence of stalks of homology sheaves. It is deduced from the Weil distinguished
  triangles of `ProEtale.CondensedRing.WeilBoundedConstructible.IsDistTriang` and the
  composition isomorphisms `weilLowerShriekCompIso`.
- `ProEtale.CondensedRing.weilStalkTraceAlternatingSum_weilUpperStar`: the local trace of a pullback
  `g^* K` at `w̄` is the local trace of `K` at `w̄ ≫ g`. It is deduced from the pullback of Weil
  sheaves `ProEtale.CondensedRing.weilSheafUpperStar`. Its model-Frobenius analogue is
  `ProEtale.CondensedRing.WeilBoundedConstructible.trace_stalkFrobenius_weilUpperStar`.

## Sorried inputs

- `ProEtale.CondensedRing.nonempty_homologyFunctor_weilUpperStar_iso`
  (`WeilConjectures.TraceFormula.WeilSheafUpperStar`): `Hʲ(Lg^* K) ≅ g^* Hʲ(K)` as Weil sheaves.

The triangle inputs are proved: the additivity of the local trace along distinguished triangles
(`ProEtale.CondensedRing.weilStalkTraceAlternatingSum_eq_add_of_isDistTriang`,
`WeilConjectures.TraceFormula.WeilDistTriangTrace`), the preservation of distinguished triangles by
`Rf_!` (`ProEtale.CondensedRing.WeilBoundedConstructible.IsDistTriang.weilLowerShriek_map`,
`WeilConjectures.TraceFormula.WeilDistTriangLowerShriek`) and the localization triangle
`j_! j^* K ⟶ K ⟶ i_* i^* K ⟶` of Weil objects
(`ProEtale.CondensedRing.exists_isDistTriang_openClosed`).

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y W : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
  (eX : X ≅ X) (eY : Y ≅ Y) (eW : W ≅ W)

/-- **Stalks of a pullback of Weil objects**: for `g : W ⟶ X` with
`e_W ≫ g = g ≫ e_X` and a point `w̄` of `W` of degree `n + 1`,
`t_{n+1}(g^* K; w̄) = t_{n+1}(K; w̄ ≫ g)`. -/
theorem weilStalkTraceAlternatingSum_weilUpperStar {g : W ⟶ X} (hg : eW.hom ≫ g = g ≫ eX.hom)
    (K : WeilBoundedConstructible ℓ eX.hom) (n : ℕ) (w : frobeniusFixedPoints eW (n + 1)) :
    weilStalkTraceAlternatingSum ℓ (n + 1) w.1 w.2.2 ((weilUpperStar ℓ eW.hom eX.hom g hg).obj K) =
      weilStalkTraceAlternatingSum ℓ (n + 1) (frobeniusFixedPointsMap eW eX hg n w).1
        (frobeniusFixedPointsMap eW eX hg n w).2.2 K :=
by
  rw [weilStalkTraceAlternatingSum, weilStalkTraceAlternatingSum]
  refine finsum_congr fun j ↦ congrArg _ ?_
  obtain ⟨φ⟩ := nonempty_homologyFunctor_weilUpperStar_iso ℓ eX eW hg K j
  rw [weilSheafStalkTrace_congr ℓ (n + 1) w.1 w.2.2 φ]
  exact weilSheafStalkTrace_weilSheafUpperStar ℓ eX eW hg _ n w

section Points

variable {V : Over (Spec (.of k))} {eV : V ≅ V} {m : V ⟶ X} [Mono m.left]
  (hm : eV.hom ≫ m = m ≫ eX.hom)

include hm in
omit [Finite k] [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] in
/-- The restriction of an automorphism of finite order to a stable monomorphism has finite
order. -/
lemma exists_pow_eq_refl_of_mono (heX : ∃ m : ℕ, eX.pow (m + 1) = Iso.refl X) :
    ∃ m : ℕ, eV.pow (m + 1) = Iso.refl V := by
  obtain ⟨r, hr⟩ := heX
  refine ⟨r, Iso.ext (Over.OverMorphism.ext ?_)⟩
  rw [← cancel_mono m.left, ← Over.comp_left, Iso.pow_hom_comp_eq_comp_pow_hom eV eX hm r,
    hr]
  simp

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] in
/-- A point of `X` of degree `n + 1` in the image of a monomorphism `m` stable under `e_X` lifts
to a point of `V` of degree `n + 1`. -/
lemma exists_frobeniusFixedPointsMap_eq {n : ℕ} (x : frobeniusFixedPoints eX (n + 1))
    (u : Spec (.of (AlgebraicClosure k)) ⟶ V.left) (hu : u ≫ m.left = x.1) :
    ∃ v : frobeniusFixedPoints eV (n + 1), frobeniusFixedPointsMap eV eX hm n v = x := by
  refine ⟨⟨u, ?_, ?_⟩, Subtype.ext hu⟩
  · rw [← Over.w m, ← Category.assoc, hu, x.2.1]
  · rw [← cancel_mono m.left, Category.assoc, ← Over.comp_left,
      Iso.pow_hom_comp_eq_comp_pow_hom eV eX hm n, Over.comp_left, ← Category.assoc, hu,
      x.2.2, Category.assoc, hu]

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] in
/-- The points of `X` over `ȳ` in the image of a monomorphism `m` are the points of `V` over
`ȳ`. -/
lemma bijective_frobeniusFixedPointsMap_fiber {f : X ⟶ Y} (n : ℕ)
    (y : frobeniusFixedPoints eY (n + 1)) (P : Set (frobeniusFixedPoints eX (n + 1)))
    (hP : ∀ x, x ∈ P ↔ ∃ u : Spec (.of (AlgebraicClosure k)) ⟶ V.left, u ≫ m.left = x.1) :
    Function.Bijective (fun v : {v : frobeniusFixedPoints eV (n + 1) // v.1 ≫ (m ≫ f).left = y.1} ↦
      (⟨⟨frobeniusFixedPointsMap eV eX hm n v.1, by
          simpa only [frobeniusFixedPointsMap, Over.comp_left, Category.assoc] using v.2⟩,
        (hP _).2 ⟨v.1.1, rfl⟩⟩ :
        {x : {x : frobeniusFixedPoints eX (n + 1) // x.1 ≫ f.left = y.1} // x.1 ∈ P})) := by
  constructor
  · intro v₁ v₂ h
    refine Subtype.ext (Subtype.ext ?_)
    have := congrArg (fun x ↦ x.1.1.1) h
    exact (cancel_mono m.left).1 this
  · rintro ⟨⟨x, hx⟩, hxP⟩
    obtain ⟨u, hu⟩ := (hP x).1 hxP
    obtain ⟨v, rfl⟩ := exists_frobeniusFixedPointsMap_eq eX hm x u hu
    exact ⟨⟨v, by simpa only [frobeniusFixedPointsMap, Over.comp_left, Category.assoc] using hx⟩,
      rfl⟩

end Points

variable {U Z : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  (eU : U ≅ U) (eZ : Z ≅ Z) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)
  {j : U ⟶ X} {i : Z ⟶ X} [IsOpenImmersion j.left] [IsClosedImmersion i.left]
  (hj : eU.hom ≫ j = j ≫ eX.hom) (hi : eZ.hom ≫ i = i ≫ eX.hom)

omit [Finite k] in
include hj in
/-- The counit of `Rj_! ⊣ Lj^*` is compatible with the Frobenius base changes. -/
lemma map_counit_app_eq_weilLowerShriekComparison
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ eX.hom).map
        ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K) =
      (weilLowerShriekComparison ℓ eU eX hj).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K) ≫
        (boundedConstructibleLowerShriek ℓ j).map
          ((weilUpperStarComparison ℓ eU.hom eX.hom j hj).hom.app K) ≫
        (boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ eX.hom).obj K) := by
  have sq := isPullback_of_comp_eq_of_isOpenImmersion j hj
  have hC1 := boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isOpenImmersion ℓ sq
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)
  have hEx := Adjunction.exchangeLeft_app_comp_map_counit_app
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ j)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ j)
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
      sq.toCommSq.flip) K
  rw [← boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_exchangeLeft
    (Profinite.padicAlgClRingObj ℓ) ℓ sq.toCommSq] at hEx
  have hn := (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ
      j).hom.naturality ((boundedConstructiblePullbackSquareComparison
        (Profinite.padicAlgClRingObj ℓ) ℓ sq.toCommSq.flip).hom.app K)
  rw [boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl,
    counit_app_ofNatIsoRight_upperShriekIsoUpperStar,
    counit_app_ofNatIsoRight_upperShriekIsoUpperStar,
    weilUpperStarComparison_hom_app_eq ℓ j hj sq.toCommSq.flip, weilLowerShriekComparison_hom,
    Functor.map_comp, ← hC1]
  simp only [Category.assoc]
  rw [hEx, reassoc_of% hn]


omit [Finite k] in
/-- The counit `Rj_! Lj^* K ⟶ K` is a morphism of Weil objects. -/
lemma counit_comm_weilStr (K : WeilBoundedConstructible ℓ eX.hom) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ eX.hom).map
        ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app
          K.carrier) ≫ K.str.hom =
      ((weilLowerShriek ℓ eU eX hj).obj ((weilUpperStar ℓ eU.hom eX.hom j hj).obj K)).str.hom ≫
        (boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app
          K.carrier := by
  rw [map_counit_app_eq_weilLowerShriekComparison ℓ eX eU hj K.carrier,
    weilLowerShriek_obj_str, weilUpperStar_obj_str]
  have hn := (boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.naturality
    K.str.hom
  simp only [Functor.comp_map, Functor.id_map] at hn
  change _ = ((weilLowerShriekComparison ℓ eU eX hj).hom.app _ ≫
      (boundedConstructibleLowerShriek ℓ j).map
        ((weilUpperStarComparison ℓ eU.hom eX.hom j hj).hom.app K.carrier ≫
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).map K.str.hom)) ≫
      (boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K.carrier
  simp only [Functor.map_comp, Category.assoc]
  rw [hn]

omit [Finite k] [IsClosedImmersion i.left] in
/-- The Frobenius comparison of the pullback is the inverse of the pullback comparison of any
proof of the commutativity of the Frobenius square. -/
lemma weilUpperStarComparison_eq_symm (sq : CommSq eZ.hom i i eX.hom) :
    weilUpperStarComparison ℓ eZ.hom eX.hom i hi =
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ sq).symm :=
  rfl

omit [Finite k] [IsClosedImmersion i.left] in
/-- The pullback comparison of the Frobenius square of `i` is inverse to the Frobenius comparison
of the pullback along `i`. -/
lemma pullbackSquareComparison_hom_app_comp_weilUpperStarComparison_hom_app
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
      (weilFrobeniusSquare eZ eX hi).toCommSq).hom.app K ≫
      (weilUpperStarComparison ℓ eZ.hom eX.hom i hi).hom.app K = 𝟙 _ := by
  rw [weilUpperStarComparison_eq_symm ℓ eX eZ hi (weilFrobeniusSquare eZ eX hi).toCommSq,
    Iso.symm_hom, Iso.hom_inv_id_app]

omit [Finite k] in
/-- The unit `K ⟶ Ri_! Li^* K` is a morphism of Weil objects. -/
lemma unit_comm_weilStr (K : WeilBoundedConstructible ℓ eX.hom) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ eX.hom).map
        ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ i).unit.app K.carrier) ≫
      ((weilLowerShriek ℓ eZ eX hi).obj ((weilUpperStar ℓ eZ.hom eX.hom i hi).obj K)).str.hom =
        K.str.hom ≫
          (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ i).unit.app
            K.carrier := by
  rw [weilLowerShriek_obj_str, weilUpperStar_obj_str]
  change _ ≫ (weilLowerShriekComparison ℓ eZ eX hi).hom.app _ ≫
      (boundedConstructibleLowerShriek ℓ i).map
        ((weilUpperStarComparison ℓ eZ.hom eX.hom i hi).hom.app K.carrier ≫
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map K.str.hom) = _
  rw [weilLowerShriekComparison_hom, reassoc_of%
    (map_unit_app_comp_boundedConstructibleLowerShriekBaseChange_padicAlgCl_app ℓ
      (weilFrobeniusSquare eZ eX hi) K.carrier), ← Functor.map_comp,
    reassoc_of% (pullbackSquareComparison_hom_app_comp_weilUpperStarComparison_hom_app ℓ eX eZ hi
      K.carrier)]
  exact ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ i).unit.naturality
    K.str.hom).symm

omit [Finite k] in
/-- **The localization triangle of Weil objects** (blueprint
`proposition-extension-zero-restriction-closed-subscheme--8` and
`lemma-additivity-open-subscheme-complement`, Step 2): for an open immersion `j` with closed
complement `i`, both stable under `e_X`, the counit `Rj_! Lj^* K ⟶ K` and the unit `K ⟶ Ri_! Li^* K`
are morphisms of Weil objects (`counit_comm_weilStr`, `unit_comm_weilStr`) and extend to a
distinguished triangle of Weil objects. The triangle is
`ProEtale.CondensedRing.exists_distTriang_openClosed`, through `Ri_! ≅ Ri_*`; the Frobenius
compatibility of its connecting morphism is
`ProEtale.CondensedRing.map_comp_connecting_eq_of_isCompl`. -/
theorem exists_isDistTriang_openClosed
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (K : WeilBoundedConstructible ℓ eX.hom) :
    ∃ (α : (weilLowerShriek ℓ eU eX hj).obj ((weilUpperStar ℓ eU.hom eX.hom j hj).obj K) ⟶ K)
      (β : K ⟶ (weilLowerShriek ℓ eZ eX hi).obj ((weilUpperStar ℓ eZ.hom eX.hom i hi).obj K)),
      WeilBoundedConstructible.IsDistTriang ℓ α β := by
  have : IsIso eX.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eX.hom))
  have : IsIso eU.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eU.hom))
  let e := (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i).app
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)
  have hunit : (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ i).unit.app
      K.carrier ≫ e.hom = (boundedConstructibleUpperStarLowerStarAdjunction
        ℓ i).unit.app K.carrier := by
    simp [e, boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl]
  obtain ⟨δ, hδ⟩ := exists_distTriang_openClosed ℓ j i hcompl K.carrier
  refine ⟨ObjectProperty.homMk ⟨_, (counit_comm_weilStr ℓ eX eU hj K).trans (by rfl)⟩,
    ObjectProperty.homMk ⟨_, unit_comm_weilStr ℓ eX eZ hi K⟩,
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map e.hom ≫
      δ, ?_, ?_⟩
  · refine Pretriangulated.isomorphic_distinguished _ hδ _
      (Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          X.left)).ι.mapIso e) ?_ ?_ ?_)
    all_goals first
      | exact (Category.comp_id _).trans (Category.id_comp _).symm
      | exact ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          X.left)).ι.map_comp _ _).symm.trans ((congrArg (boundedConstructible
            (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map hunit).trans
              (Category.id_comp _).symm)
      | exact (congrArg (((boundedConstructible (condensedRingObj
          (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map e.hom ≫ δ) ≫ ·)
            ((shiftFunctor _ (1 : ℤ)).map_id _)).trans (Category.comp_id _)
  · have hb : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ eX.hom).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
          i).unit.app K.carrier) ≫
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ eX.hom).map e.inv ≫
          ((weilLowerShriek ℓ eZ eX hi).obj ((weilUpperStar ℓ eZ.hom eX.hom i hi).obj K)).str.hom ≫
            e.hom) =
        K.str.hom ≫ (boundedConstructibleUpperStarLowerStarAdjunction
          ℓ i).unit.app K.carrier := by
      rw [← hunit]
      simp only [Functor.map_comp, Category.assoc]
      rw [← Functor.map_comp_assoc _ e.hom e.inv, e.hom_inv_id, CategoryTheory.Functor.map_id,
        Category.id_comp]
      exact ((Category.assoc _ _ _).symm.trans ((unit_comm_weilStr ℓ eX eZ hi K) =≫ e.hom)).trans
        (Category.assoc _ _ _)
    have key := map_comp_connecting_eq_of_isCompl ℓ hcompl hj K.carrier δ hδ _ _ _
      (counit_comm_weilStr ℓ eX eU hj K) hb
    have h1 := connectingOfIso_comp
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ eX.hom)
      (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
      (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι _
      (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ eX.hom) e.hom δ
    have h2 : ((weilLowerShriek ℓ eZ eX hi).obj
        ((weilUpperStar ℓ eZ.hom eX.hom i hi).obj K)).str.hom ≫
        e.hom =
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ eX.hom).map e.hom ≫
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ eX.hom).map e.inv ≫
            ((weilLowerShriek ℓ eZ eX hi).obj
              ((weilUpperStar ℓ eZ.hom eX.hom i hi).obj K)).str.hom ≫
              e.hom := by
      rw [← Functor.map_comp_assoc, e.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
    exact ((Functor.map_comp_assoc _ _ _ _).symm.trans
      ((congrArg (fun x ↦ (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        X.left)).ι.map x ≫ δ) h2).trans (Functor.map_comp_assoc _ _ _ _))).trans
      ((congrArg (_ ≫ ·) key).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h1.symm)))


/-- **Additivity of the local trace along an open–closed decomposition**: for
an open immersion `j` with closed complement `i`, both stable under `e_X`,
`t(Rf_! K; ȳ) = t(R(j ≫ f)_! j^* K; ȳ) + t(R(i ≫ f)_! i^* K; ȳ)`. -/
theorem weilStalkTraceAlternatingSum_weilLowerShriek_eq_add
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (K : WeilBoundedConstructible ℓ eX.hom) (n : ℕ) (y : frobeniusFixedPoints eY (n + 1)) :
    weilStalkTraceAlternatingSum ℓ (n + 1) y.1 y.2.2 ((weilLowerShriek ℓ eX eY hf).obj K) =
      weilStalkTraceAlternatingSum ℓ (n + 1) y.1 y.2.2
          ((weilLowerShriek ℓ eU eY (comp_comm_of_comp_comm eU eY eX hj hf)).obj
            ((weilUpperStar ℓ eU.hom eX.hom j hj).obj K)) +
        weilStalkTraceAlternatingSum ℓ (n + 1) y.1 y.2.2
          ((weilLowerShriek ℓ eZ eY (comp_comm_of_comp_comm eZ eY eX hi hf)).obj
            ((weilUpperStar ℓ eZ.hom eX.hom i hi).obj K)) :=
by
  obtain ⟨α, β, h⟩ := exists_isDistTriang_openClosed ℓ eX eU eZ hj hi hcompl K
  rw [weilStalkTraceAlternatingSum_eq_add_of_isDistTriang ℓ n y.1 y.2.2
      (h.weilLowerShriek_map ℓ eX eY hf),
    weilStalkTraceAlternatingSum_congr ℓ n y.1 y.2.2 (weilLowerShriekCompIso ℓ eU eY eX hj hf _),
    weilStalkTraceAlternatingSum_congr ℓ n y.1 y.2.2 (weilLowerShriekCompIso ℓ eZ eY eX hi hf _)]

/-- **Dévissage along an open–closed decomposition**: the sheaf–function compatibility along
`j ≫ f` and along `i ≫ f` gives it along `f`, for an automorphism `e_X` of finite order. -/
theorem shriekTraceFunctionAt_of_isCompl
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (heX : ∃ m : ℕ, eX.pow (m + 1) = Iso.refl X)
    (HU : ShriekTraceFunctionAt ℓ eU eY (comp_comm_of_comp_comm eU eY eX hj hf))
    (HZ : ShriekTraceFunctionAt ℓ eZ eY (comp_comm_of_comp_comm eZ eY eX hi hf)) :
    ShriekTraceFunctionAt ℓ eX eY hf := by
  intro K n y
  rw [weilStalkTraceAlternatingSum_weilLowerShriek_eq_add ℓ eX eY eU eZ hf hj hi hcompl K n y, HU,
      HZ]
  simp only [weilStalkTraceAlternatingSum_weilUpperStar]
  classical
  have := finite_frobeniusFixedPoints_of_pow_eq_refl eX heX n
  have := finite_frobeniusFixedPoints_of_pow_eq_refl eU
    (exists_pow_eq_refl_of_mono eX hj heX) n
  have := finite_frobeniusFixedPoints_of_pow_eq_refl eZ
    (exists_pow_eq_refl_of_mono eX hi heX) n
  let := Fintype.ofFinite (frobeniusFixedPoints eX (n + 1))
  let := Fintype.ofFinite (frobeniusFixedPoints eU (n + 1))
  let := Fintype.ofFinite (frobeniusFixedPoints eZ (n + 1))
  simp only [finsum_eq_sum_of_fintype]
  let P : Set (frobeniusFixedPoints eX (n + 1)) := {x | x.1.base default ∈ Set.range j.left.base}
  have hPU : ∀ x, x ∈ P ↔ ∃ u : Spec (.of (AlgebraicClosure k)) ⟶ U.left, u ≫ j.left = x.1 := by
    intro x
    refine ⟨fun hx ↦ ⟨IsOpenImmersion.lift j.left x.1 ?_, IsOpenImmersion.lift_fac _ _ _⟩, ?_⟩
    · rintro _ ⟨a, rfl⟩
      rwa [Subsingleton.elim a default]
    · rintro ⟨u, hu⟩
      exact ⟨u.base default, by rw [← hu]; rfl⟩
  have hPZ : ∀ x, x ∈ Pᶜ ↔ ∃ z : Spec (.of (AlgebraicClosure k)) ⟶ Z.left, z ≫ i.left = x.1 := by
    intro x
    have hrange : x.1.base default ∈ Set.range i.left.base ↔ x ∈ Pᶜ := by
      rw [Set.mem_compl_iff, Set.mem_ofPred_eq, ← Set.mem_compl_iff, hcompl.compl_eq.symm]
    rw [← hrange]
    refine ⟨fun hx ↦ ⟨IsClosedImmersion.lift i.left x.1 ?_, IsClosedImmersion.lift_fac _ _ _⟩, ?_⟩
    · rw [Scheme.IdealSheafData.le_ker_iff_range_subset_support, Scheme.Hom.support_ker,
        i.left.isClosedMap.isClosed_range.closure_eq]
      rintro _ ⟨a, rfl⟩
      rwa [Subsingleton.elim a default]
    · rintro ⟨z, hz⟩
      exact ⟨z.base default, by rw [← hz]; rfl⟩
  rw [← Fintype.sum_subtype_add_sum_subtype
    (p := fun x : {x : frobeniusFixedPoints eX (n + 1) // x.1 ≫ f.left = y.1} ↦ x.1 ∈ P)
    (f := fun x ↦ weilStalkTraceAlternatingSum ℓ (n + 1) x.1.1 x.1.2.2 K)]
  congr 1
  · exact Fintype.sum_bijective _ (bijective_frobeniusFixedPointsMap_fiber eX eY hj n y P hPU)
      (fun v ↦ weilStalkTraceAlternatingSum ℓ (n + 1) (frobeniusFixedPointsMap eU eX hj n v.1).1
        (frobeniusFixedPointsMap eU eX hj n v.1).2.2 K)
      (fun x ↦ weilStalkTraceAlternatingSum ℓ (n + 1) x.1.1.1 x.1.1.2.2 K) fun _ ↦ rfl
  · exact Fintype.sum_bijective _ (bijective_frobeniusFixedPointsMap_fiber eX eY hi n y Pᶜ hPZ)
      (fun v ↦ weilStalkTraceAlternatingSum ℓ (n + 1) (frobeniusFixedPointsMap eZ eX hi n v.1).1
        (frobeniusFixedPointsMap eZ eX hi n v.1).2.2 K)
      (fun x ↦ weilStalkTraceAlternatingSum ℓ (n + 1) x.1.1.1 x.1.1.2.2 K) fun _ ↦ rfl

end AlgebraicGeometry.ProEtale.CondensedRing
