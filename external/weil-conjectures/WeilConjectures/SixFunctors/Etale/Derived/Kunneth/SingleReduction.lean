/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatDevissage
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.TensorBaseChange

/-!
# Reduction of the base change map to single sheaves

For a commutative square `h ≫ f' = e ≫ g` of schemes and `p : X' ⟶ X`, consider the base change
map (`AlgebraicGeometry.Etale.tensorBaseChangeMap`)

`Lp^* E ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* Lp^* E ⊗ᴸ Le^* F)`.

We show that it is an isomorphism for every `E` of Tor amplitude in `[n, ∞)` and every bounded
below `F` as soon as it is an isomorphism when `E` is a flat sheaf and `F` is a sheaf, both
placed in degree `0` (`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_of_single`). This is the
first part of the proof of blueprint `lemma-kunneth-field-coefficients--1`.

* In the variable `F`, for `E` a flat sheaf: both sides do not lower the cohomological degree, so
  in a fixed degree they only depend on a truncation `τ^{≤ q} F`, which is bounded
  (`DerivedCategory.isIso_app_of_isGE`).
* In the variable `E`: represent `E` by a complex `P` of flat sheaves whose pullbacks are K-flat.
  For `N` large, the stupid truncation `σ^{≥ N + 1} P` has K-flat pullbacks concentrated in
  degrees `≥ N + 1`, so both sides vanish on it in low degrees; and `σ^{≤ N} P` has Tor amplitude
  in `[n, N]`, hence is represented by a strictly bounded complex of flat sheaves, which is
  handled by the stupid truncations
  (`DerivedCategory.isIso_app_Q_obj_of_isStrictlyGE_of_isStrictlyLE_of_prop`).

The blueprint truncates a bounded below flat model of `E` directly; such a complex need not be
K-flat, which is why we truncate the K-flat flat resolution instead.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

/-- Every complex of étale sheaves on `X` has a resolution `P ⟶ L` by a K-flat complex `P` of
flat sheaves all of whose pullbacks `g^* P` are K-flat: the functorial flat resolution. -/
lemma exists_quasiIso_flat_kFlat_upperStar {X : Scheme.{u}}
    (L : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) :
    ∃ (P : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) (π : P ⟶ L), QuasiIso π ∧
      (∀ n, ObjectProperty.flat (P.X n)) ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P ∧
      ∀ {Z : Scheme.{u}} (g : Z ⟶ X), (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
        (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj P) := by
  have (Y : Sheaf X.smallEtaleTopology A) :
      PreservesColimitsOfShape ℤ ((curriedTensor (Sheaf X.smallEtaleTopology A)).flip.obj Y) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft Y)
      (NatIso.ofComponents (fun Z ↦ β_ Y Z) (by intros; simp [curriedTensor]))
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ Sheaf X.smallEtaleTopology A))).reduced
  refine ⟨Λ.resolutionFunctor.obj L, Λ.resolutionNatTrans.app L, inferInstance, fun n ↦ ?_,
    Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le L, fun g ↦ ?_⟩
  · have := CochainComplex.closedUnderColimitsOfShape_flat (Sheaf X.smallEtaleTopology A) ℤ
    let c := Λ.colimitOfShapeResolutionFunctorObj L
    exact ObjectProperty.prop_of_isColimit _
      (isColimitOfPreserves (HomologicalComplex.eval _ (.up ℤ) n) c.isColimit)
      (fun i ↦ ObjectProperty.flat.essImage_ι_le _ ((c.prop_diag_obj i).1 n))
  · exact kFlat_upperStar_mapHomologicalComplex_obj g
      (Λ.colimitOfShapeFlatResolutionFunctorObj ObjectProperty.flat.essImage_ι_le L).colimitsOfShape

omit [UpperStarPreservesFlat A] in
/-- The derived pullback `Lg^*` preserves the objects concentrated in degrees `≥ d`. -/
lemma isGE_leftDerivedUpperStar_obj {X Z : Scheme.{u}} (g : Z ⟶ X)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) (d : ℤ) [K.IsGE d] :
    (L((g)^*[A]).obj K).IsGE d :=
  have := (g)^*[A].isGE_mapDerivedCategory_obj K d
  _root_.DerivedCategory.TStructure.t.isGE_of_iso
    ((leftDerivedUpperStarIsoMapDerivedCategory A g).app K).symm d

omit [UpperStarPreservesFlat A] in
/-- If `R` is a complex concentrated in degrees `≥ c` whose pullback `g^* R` is K-flat, then
`Lg^* R ⊗ᴸ N` is concentrated in degrees `≥ c + d` for every `N` concentrated in degrees
`≥ d`. -/
lemma isGE_derivedTensor_leftDerivedUpperStar_obj_Q_obj {X Z : Scheme.{u}} (g : Z ⟶ X)
    (R : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) (c : ℤ) [R.IsStrictlyGE c]
    (hR : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj R))
    (N : DerivedCategory (Sheaf Z.smallEtaleTopology A)) (d : ℤ) [N.IsGE d] :
    (((-⊗ᴸ-(Z)[A]).obj (L((g)^*[A]).obj (_root_.DerivedCategory.Q.obj R))).obj N).IsGE
      (c + d) := by
  have : CochainComplex.IsStrictlyGE (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj R) c :=
    (CochainComplex.isStrictlyGE_iff _ c).2 fun i hi ↦
      (g)^*[A].map_isZero (CochainComplex.isZero_of_isStrictlyGE R c i hi)
  have := _root_.DerivedCategory.isGE_Q_obj_tensor_of_kFlat _ hR c N d
  have e : L((g)^*[A]).obj (_root_.DerivedCategory.Q.obj R) ≅
      _root_.DerivedCategory.Q.obj (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj R) :=
    (leftDerivedUpperStarIsoMapDerivedCategory A g).app _ ≪≫
      (g)^*[A].mapDerivedCategoryFactors.app R
  exact _root_.DerivedCategory.TStructure.t.isGE_of_iso (whiskerRightIso e N).symm _

/-- If `𝓔` is a flat sheaf on `X`, then `Lg^* 𝓔 ⊗ᴸ N` is concentrated in degrees `≥ d` for every
`N` concentrated in degrees `≥ d`. -/
lemma isGE_derivedTensor_leftDerivedUpperStar_singleFunctor_obj {X Z : Scheme.{u}} (g : Z ⟶ X)
    (𝓔 : Sheaf X.smallEtaleTopology A) (h𝓔 : ObjectProperty.flat 𝓔)
    (N : DerivedCategory (Sheaf Z.smallEtaleTopology A)) (d : ℤ) [N.IsGE d] :
    (((-⊗ᴸ-(Z)[A]).obj (L((g)^*[A]).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj 𝓔))).obj N).IsGE d := by
  have hR : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat (((g)^*[A].mapHomologicalComplex
      (.up ℤ)).obj ((HomologicalComplex.single _ (.up ℤ) 0).obj 𝓔)) :=
    ObjectProperty.prop_of_iso _
      ((HomologicalComplex.singleMapHomologicalComplex (g)^*[A] (.up ℤ) 0).app 𝓔).symm
      ((CochainComplex.kFlat_single_obj_iff_flat _ 0).2
        (Functor.PreservesFlat.flat_obj (F := (g)^*[A]) h𝓔))
  have : _root_.DerivedCategory.TStructure.t.IsGE (L((g)^*[A]).obj (_root_.DerivedCategory.Q.obj
      ((HomologicalComplex.single _ (.up ℤ) 0).obj 𝓔)) ⊗ N) (0 + d) :=
    isGE_derivedTensor_leftDerivedUpperStar_obj_Q_obj A g _ 0 hR N d
  have e : _root_.DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj 𝓔) ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj 𝓔 :=
    ((_root_.DerivedCategory.singleFunctorIsoCompQ _ 0).app 𝓔).symm
  have h := _root_.DerivedCategory.TStructure.t.isGE_of_iso
    (whiskerRightIso (L((g)^*[A]).mapIso e) N) (0 + d)
  rwa [zero_add] at h

omit [UpperStarPreservesFlat A] in
/-- If `L(h ≫ p)^* K ⊗ᴸ N` is concentrated in degrees `≥ d`, so is `Lh^* Lp^* K ⊗ᴸ N`. -/
lemma isGE_derivedTensor_leftDerivedUpperStar_comp_obj {X X' Y : Scheme.{u}} (h : Y ⟶ X')
    (p : X' ⟶ X) (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (N : DerivedCategory (Sheaf Y.smallEtaleTopology A)) (d : ℤ)
    (hK : (((-⊗ᴸ-(Y)[A]).obj (L((h ≫ p)^*[A]).obj K)).obj N).IsGE d) :
    (((-⊗ᴸ-(Y)[A]).obj (L((h)^*[A]).obj (L((p)^*[A]).obj K))).obj N).IsGE d :=
  have : _root_.DerivedCategory.TStructure.t.IsGE (L((h ≫ p)^*[A]).obj K ⊗ N) d := hK
  _root_.DerivedCategory.TStructure.t.isGE_of_iso
    (whiskerRightIso ((leftDerivedUpperStarComp A h p).app K) N) d

omit [UpperStarPreservesFlat A] in
/-- Let `P` be a K-flat complex of flat sheaves such that `P ⊗ᴸ 𝓜` vanishes in degrees `< n` for
every sheaf `𝓜`. For `N ≥ n`, the stupid truncation `σ^{≤ N} P` has Tor amplitude in `[n, N]`:
the fiber `σ^{≥ N + 1} P` of `P ⟶ σ^{≤ N} P` is a K-flat complex concentrated in degrees
`≥ N + 1`. -/
lemma torAmplitudeIn_Q_obj_stupidTruncLE {X : Scheme.{u}}
    (P : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) (hP : ∀ i, ObjectProperty.flat (P.X i))
    (hPk : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) (n N : ℤ) (hNn : n ≤ N)
    (hE : ∀ (𝓜 : Sheaf X.smallEtaleTopology A) (q : ℤ), q < n →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        (((-⊗ᴸ-(X)[A]).obj (_root_.DerivedCategory.Q.obj P)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj 𝓜)))) :
    _root_.DerivedCategory.torAmplitudeIn _ n N
      (_root_.DerivedCategory.Q.obj (P.stupidTrunc (ComplexShape.embeddingUpIntLE N))) := by
  intro 𝓜
  have ac := ComplexShape.Embedding.embeddingUpInt_areComplementary N (N + 1) rfl
  have hS : (P.shortComplexStupidTrunc ac).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _
      fun i ↦ (P.shortComplexStupidTruncSplitting ac i).shortExact
  refine ⟨?_, ?_⟩
  · have hT := rot_of_distTriang _ (((-⊗ᴸ-(X)[A]).flip.obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj 𝓜)).map_distinguished _
        (_root_.DerivedCategory.triangleOfSES_distinguished hS))
    refine _root_.DerivedCategory.TStructure.t.isGE₂ _ hT n ?_ ?_
    · exact (_root_.DerivedCategory.isGE_iff _ n).2 (hE 𝓜)
    · have := _root_.DerivedCategory.isGE_Q_obj_tensor_of_kFlat _
        (CochainComplex.kFlat_stupidTruncGE P hP hPk N) (N + 1)
        ((_root_.DerivedCategory.singleFunctor _ 0).obj 𝓜) 0
      have := _root_.DerivedCategory.TStructure.t.isGE_shift
        (_root_.DerivedCategory.Q.obj (P.stupidTrunc (ComplexShape.embeddingUpIntGE (N + 1))) ⊗
          (_root_.DerivedCategory.singleFunctor _ 0).obj 𝓜) (N + 1 + 0) 1 N (by lia)
      exact _root_.DerivedCategory.TStructure.t.isGE_of_ge
        ((_root_.DerivedCategory.Q.obj (P.stupidTrunc (ComplexShape.embeddingUpIntGE (N + 1))) ⊗
          (_root_.DerivedCategory.singleFunctor _ 0).obj 𝓜)⟦(1 : ℤ)⟧) n N hNn
  · have := _root_.DerivedCategory.isLE_tensor (_root_.DerivedCategory.Q.obj
      (P.stupidTrunc (ComplexShape.embeddingUpIntLE N)))
      ((_root_.DerivedCategory.singleFunctor _ 0).obj 𝓜) N 0
    exact _root_.DerivedCategory.TStructure.t.isLE_of_le _ (N + 0) N (by lia)

section BaseChange

variable {X X' S' T Y : Scheme.{u}} (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S') (g : T ⟶ S')
  (w : h ≫ f' = e ≫ g)

/-- Reduction of the base change map `M ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* M ⊗ᴸ Le^* F)` to sheaves
`F` placed in degree `0`, for `M` such that `M ⊗ᴸ -` and `Lh^* M ⊗ᴸ -` do not lower the
cohomological degree: both sides then do not lower the cohomological degree in `F`. -/
lemma isIso_tensorBaseChangeMap_of_isGE_of_isIso_singleFunctor_obj
    (M : DerivedCategory (Sheaf X'.smallEtaleTopology A))
    (hM : ∀ (N : DerivedCategory (Sheaf X'.smallEtaleTopology A)) (d : ℤ), N.IsGE d →
      (((-⊗ᴸ-(X')[A]).obj M).obj N).IsGE d)
    (hM' : ∀ (N : DerivedCategory (Sheaf Y.smallEtaleTopology A)) (d : ℤ), N.IsGE d →
      (((-⊗ᴸ-(Y)[A]).obj (L((h)^*[A]).obj M)).obj N).IsGE d)
    (hs : ∀ 𝓕 : Sheaf T.smallEtaleTopology A, IsIso (tensorBaseChangeMap A h e f' g w M
      ((_root_.DerivedCategory.singleFunctor _ 0).obj 𝓕)))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology A)) (m : ℤ) [F.IsGE m] :
    IsIso (tensorBaseChangeMap A h e f' g w M F) :=
  _root_.DerivedCategory.isIso_app_of_isGE (tensorBaseChangeMapRight A h e f' g w M)
    (fun N d hN ↦ by
      have := hN
      have := (g)_*[A].isGE_rightDerivedFunctor_obj N d
      exact hM _ d (isGE_leftDerivedUpperStar_obj A f' _ d))
    (fun N d hN ↦ by
      have := hN
      have := hM' _ d (isGE_leftDerivedUpperStar_obj A e N d)
      exact (h)_*[A].isGE_rightDerivedFunctor_obj _ d)
    hs F m

omit [UpperStarPreservesFlat A] in
/-- The source `Lp^* R ⊗ᴸ Lf'^* Rg_* F` of the base change map is concentrated in degrees
`≥ c + m` if `R` is concentrated in degrees `≥ c` with `p^* R` K-flat and `F` is concentrated in
degrees `≥ m`. -/
lemma isGE_tensorBaseChangeMap_source_Q_obj (p : X' ⟶ X)
    (F : DerivedCategory (Sheaf T.smallEtaleTopology A)) (m : ℤ) [F.IsGE m]
    (R : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) (c : ℤ) [R.IsStrictlyGE c]
    (hR : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((p)^*[A].mapHomologicalComplex (.up ℤ)).obj R)) :
    ((L((p)^*[A]) ⋙ (-⊗ᴸ-(X')[A]).flip.obj (L((f')^*[A]).obj (R((g)_*[A]).obj F))).obj
      (_root_.DerivedCategory.Q.obj R)).IsGE (c + m) :=
  have := (g)_*[A].isGE_rightDerivedFunctor_obj F m
  have := isGE_leftDerivedUpperStar_obj A f' (R((g)_*[A]).obj F) m
  isGE_derivedTensor_leftDerivedUpperStar_obj_Q_obj A p R c hR _ m

omit [UpperStarPreservesFlat A] in
/-- The target `Rh_* (Lh^* Lp^* R ⊗ᴸ Le^* F)` of the base change map is concentrated in degrees
`≥ c + m` if `R` is concentrated in degrees `≥ c` with `(h ≫ p)^* R` K-flat and `F` is
concentrated in degrees `≥ m`. -/
lemma isGE_tensorBaseChangeMap_target_Q_obj (p : X' ⟶ X)
    (F : DerivedCategory (Sheaf T.smallEtaleTopology A)) (m : ℤ) [F.IsGE m]
    (R : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) (c : ℤ) [R.IsStrictlyGE c]
    (hR : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      ((((h ≫ p))^*[A].mapHomologicalComplex (.up ℤ)).obj R)) :
    ((L((p)^*[A]) ⋙ L((h)^*[A]) ⋙ (-⊗ᴸ-(Y)[A]).flip.obj (L((e)^*[A]).obj F) ⋙
      R((h)_*[A])).obj (_root_.DerivedCategory.Q.obj R)).IsGE (c + m) :=
  have := isGE_leftDerivedUpperStar_obj A e F m
  have := isGE_derivedTensor_leftDerivedUpperStar_comp_obj A h p _ _ _
    (isGE_derivedTensor_leftDerivedUpperStar_obj_Q_obj A (h ≫ p) R c hR (L((e)^*[A]).obj F) m)
  (h)_*[A].isGE_rightDerivedFunctor_obj (((-⊗ᴸ-(Y)[A]).obj (L((h)^*[A]).obj
    (L((p)^*[A]).obj (_root_.DerivedCategory.Q.obj R)))).obj (L((e)^*[A]).obj F)) (c + m)

/-- The base change map is an isomorphism at every `E` of Tor amplitude in `[a, b]` if it is an
isomorphism at the flat sheaves placed in degree `0`: `E` is represented by a strictly bounded
complex of flat sheaves, which is handled by the stupid truncations. -/
lemma isIso_tensorBaseChangeMap_of_torAmplitudeIn (p : X' ⟶ X)
    (F : DerivedCategory (Sheaf T.smallEtaleTopology A))
    (hflat : ∀ 𝓔 : Sheaf X.smallEtaleTopology A, ObjectProperty.flat 𝓔 →
      IsIso (tensorBaseChangeMap A h e f' g w
        (L((p)^*[A]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj 𝓔)) F))
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A)) (a b : ℤ)
    (hE : _root_.DerivedCategory.torAmplitudeIn _ a b E) :
    IsIso (tensorBaseChangeMap A h e f' g w (L((p)^*[A]).obj E) F) := by
  obtain ⟨P₀, _, _, hP₀, ⟨e₀⟩⟩ :=
    _root_.DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn hE
  have hτ : ∀ 𝓔 : Sheaf X.smallEtaleTopology A, ObjectProperty.flat 𝓔 →
      IsIso ((Functor.whiskerLeft L((p)^*[A]) (tensorBaseChangeMapLeft A h e f' g w F)).app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj 𝓔)) := hflat
  exact (NatTrans.isIso_app_iff_of_iso
    (Functor.whiskerLeft L((p)^*[A]) (tensorBaseChangeMapLeft A h e f' g w F)) e₀).1
    (_root_.DerivedCategory.isIso_app_Q_obj_of_isStrictlyGE_of_isStrictlyLE_of_prop
      (Functor.whiskerLeft L((p)^*[A]) (tensorBaseChangeMapLeft A h e f' g w F))
      ObjectProperty.flat hτ P₀ a b hP₀)

/-- Reduction of the base change map `Lp^* E ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* Lp^* E ⊗ᴸ Le^* F)`,
for `F` bounded below and `E` of Tor amplitude in `[n, ∞)`, to flat sheaves `E` placed in degree
`0`.

Represent `E` by a complex `P` of flat sheaves whose pullbacks are K-flat. In a fixed degree `q`,
for `N` large, both sides vanish in degrees `q` and `q + 1` on `σ^{≥ N + 1} P`, so the map in
degree `q` is the one for `σ^{≤ N} P`. The latter has Tor amplitude in `[n, N]`
(`AlgebraicGeometry.Etale.torAmplitudeIn_Q_obj_stupidTruncLE`). -/
lemma isIso_tensorBaseChangeMap_of_isIso_flat (p : X' ⟶ X)
    (F : DerivedCategory (Sheaf T.smallEtaleTopology A)) (m : ℤ) [F.IsGE m]
    (hflat : ∀ 𝓔 : Sheaf X.smallEtaleTopology A, ObjectProperty.flat 𝓔 →
      IsIso (tensorBaseChangeMap A h e f' g w
        (L((p)^*[A]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj 𝓔)) F))
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A)) (n : ℤ)
    (hE : ∀ (𝓜 : Sheaf X.smallEtaleTopology A) (q : ℤ), q < n →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        (((-⊗ᴸ-(X)[A]).obj E).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj 𝓜)))) :
    IsIso (tensorBaseChangeMap A h e f' g w (L((p)^*[A]).obj E) F) := by
  obtain ⟨P, π, _, hP, hPk, hPg⟩ :=
    exists_quasiIso_flat_kFlat_upperStar A (_root_.DerivedCategory.Q.objPreimage E)
  have : IsIso (_root_.DerivedCategory.Q.map π) := by
    rwa [_root_.DerivedCategory.isIso_Q_map_iff_quasiIso]
  have eP : _root_.DerivedCategory.Q.obj P ≅ E :=
    asIso (_root_.DerivedCategory.Q.map π) ≪≫ _root_.DerivedCategory.Q.objObjPreimageIso E
  have hE' (𝓜 : Sheaf X.smallEtaleTopology A) (q : ℤ) (hq : q < n) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        (((-⊗ᴸ-(X)[A]).obj (_root_.DerivedCategory.Q.obj P)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj 𝓜))) :=
    (hE 𝓜 q hq).of_iso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
      (whiskerRightIso eP _))
  refine (NatTrans.isIso_app_iff_of_iso (Functor.whiskerLeft L((p)^*[A])
    (tensorBaseChangeMapLeft A h e f' g w F)) eP).1 ?_
  rw [_root_.DerivedCategory.isIso_iff]
  intro q
  obtain ⟨N, hNn, hNq⟩ : ∃ N : ℤ, n ≤ N ∧ q + 1 < N + 1 + m :=
    ⟨max n (q - m + 1), le_max_left _ _, by lia⟩
  have ac := ComplexShape.Embedding.embeddingUpInt_areComplementary N (N + 1) rfl
  have hS : (P.shortComplexStupidTrunc ac).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _
      fun i ↦ (P.shortComplexStupidTruncSplitting ac i).shortExact
  have hT := _root_.DerivedCategory.triangleOfSES_distinguished hS
  -- both sides vanish in low degrees on `σ^{≥ N + 1} P`
  have h₁ := isGE_tensorBaseChangeMap_source_Q_obj A f' g p F m
    (P.stupidTrunc (ComplexShape.embeddingUpIntGE (N + 1))) (N + 1)
    (CochainComplex.kFlat_mapHomologicalComplex_obj_stupidTruncGE (p)^*[A] P hP (hPg p) N)
  have h₂ := isGE_tensorBaseChangeMap_target_Q_obj A h e p F m
    (P.stupidTrunc (ComplexShape.embeddingUpIntGE (N + 1))) (N + 1)
    (CochainComplex.kFlat_mapHomologicalComplex_obj_stupidTruncGE (h ≫ p)^*[A] P hP
      (hPg (h ≫ p)) N)
  -- the map is an isomorphism at `σ^{≤ N} P`
  have h₃ : IsIso ((Functor.whiskerLeft L((p)^*[A]) (tensorBaseChangeMapLeft A h e f' g w F)).app
      (_root_.DerivedCategory.triangleOfSES hS).obj₃) :=
    isIso_tensorBaseChangeMap_of_torAmplitudeIn A h e f' g w p F hflat _ n N
      (torAmplitudeIn_Q_obj_stupidTruncLE A P hP hPk n N hNn hE')
  have hobj : (_root_.DerivedCategory.triangleOfSES hS).obj₁ =
      _root_.DerivedCategory.Q.obj (P.stupidTrunc (ComplexShape.embeddingUpIntGE (N + 1))) := rfl
  refine _root_.DerivedCategory.isIso_homologyFunctor_map_app_obj₂_of_obj₃
    (Functor.whiskerLeft L((p)^*[A]) (tensorBaseChangeMapLeft A h e f' g w F))
    (_root_.DerivedCategory.triangleOfSES hS) hT q ?_ ?_ ?_ ?_ inferInstance
  all_goals rw [hobj]
  · exact _root_.DerivedCategory.isZero_of_isGE _ (N + 1 + m) q (by lia) (hX := h₁)
  · exact _root_.DerivedCategory.isZero_of_isGE _ (N + 1 + m) (q + 1) (by lia) (hX := h₁)
  · exact _root_.DerivedCategory.isZero_of_isGE _ (N + 1 + m) q (by lia) (hX := h₂)
  · exact _root_.DerivedCategory.isZero_of_isGE _ (N + 1 + m) (q + 1) (by lia) (hX := h₂)

/-- First step of the proof of blueprint `lemma-kunneth-field-coefficients--1`: reduction to single
sheaves.

The base change map `Lp^* E ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* Lp^* E ⊗ᴸ Le^* F)` is an isomorphism
for every `E` of Tor amplitude in `[n, ∞)` and every `F` concentrated in degrees `≥ m`, provided
it is an isomorphism when `E` is a flat sheaf and `F` is a sheaf, both placed in degree `0`. -/
theorem isIso_tensorBaseChangeMap_of_single (p : X' ⟶ X)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology A)) (m n : ℤ) [F.IsGE m]
    (hE : ∀ (𝓜 : Sheaf X.smallEtaleTopology A) (q : ℤ), q < n →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        (((-⊗ᴸ-(X)[A]).obj E).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj 𝓜))))
    (hsingle : ∀ 𝓔 : Sheaf X.smallEtaleTopology A, ObjectProperty.flat 𝓔 →
      ∀ 𝓕 : Sheaf T.smallEtaleTopology A, IsIso (tensorBaseChangeMap A h e f' g w
        (L((p)^*[A]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj 𝓔))
        ((_root_.DerivedCategory.singleFunctor _ 0).obj 𝓕))) :
    IsIso (tensorBaseChangeMap A h e f' g w (L((p)^*[A]).obj E) F) :=
  isIso_tensorBaseChangeMap_of_isIso_flat A h e f' g w p F m (fun 𝓔 h𝓔 ↦
    isIso_tensorBaseChangeMap_of_isGE_of_isIso_singleFunctor_obj A h e f' g w _
      (fun N d _ ↦ isGE_derivedTensor_leftDerivedUpperStar_singleFunctor_obj A p 𝓔 h𝓔 N d)
      (fun N d _ ↦ isGE_derivedTensor_leftDerivedUpperStar_comp_obj A h p _ N d
        (isGE_derivedTensor_leftDerivedUpperStar_singleFunctor_obj A (h ≫ p) 𝓔 h𝓔 N d))
      (hsingle 𝓔 h𝓔) F m) E n hE

end BaseChange

end Etale

end AlgebraicGeometry
