/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.AffineSpace
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChangeClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
public import WeilConjectures.TraceFormula.Specialization.DeformationModel
public import WeilConjectures.TraceFormula.Specialization.ThickOriginCentre

/-!

# The deformation to the normal cone of the origin of the affine line

Let `X = 𝔸¹_k = Spec k[x]` (`AlgebraicGeometry.polyAffine k 1`) and `I = (x)` the ideal of the
origin (`AlgebraicGeometry.polyAffineHyperplane k 0`). The deformation to the normal cone of the
origin over the trait `S = Spec k'⟦t⟧` is the constant family `𝔸¹_S`, with coordinate `u = x / t`,
and the projection `𝒳 ⟶ X` (giving `ε`) is the multiplication `(u, t) ↦ t u`.

This follows from the standard pair
(`AlgebraicGeometry.Scheme.Hom.isIso_deformationSpaceToAffineSpace`,
`D_0 𝔸^n_B ≅ 𝔸^n_{𝔸¹_B}`), after identifying `Spec k[x]` with `𝔸(ULift (Fin 1); Spec k)` and `(x)`
with the ideal of the zero section.

## Main results

- `AlgebraicGeometry.Scheme.Hom.deformationSpaceToAffineSpace_affineSpaceMul`: for the standard
  pair, the projection `D_0 𝔸^n_B ⟶ 𝔸^n_B` is `(t, u) ↦ t u` in the coordinates `u_k = x_k / t`.
- `AlgebraicGeometry.ProEtale.CondensedRing.polyAffineHyperplane_eq_comap`: `(x)` is the ideal of
  the zero section under `Spec k[x] ≅ 𝔸(ULift (Fin 1); Spec k)`.
- `AlgebraicGeometry.ProEtale.CondensedRing.deformationTotalPolyAffineIso`: `𝒳 ≅ 𝔸¹_S` over `S`.
- `AlgebraicGeometry.ProEtale.CondensedRing.deformationTotalPolyAffineIso_inv_toBase`: under this
  isomorphism, `𝒳 ⟶ 𝔸¹_k` is `(u, t) ↦ t u`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

open AffineZariskiSite

variable (n : Type u) (B : Scheme.{u})

/-- The multiplication `𝔸^n_{𝔸¹_B} ⟶ 𝔸^n_B`, `(t, u) ↦ t u`. -/
noncomputable def affineSpaceMul : 𝔸(n; 𝔸(ULift.{u} (Fin 1); B)) ⟶ 𝔸(n; B) :=
  AffineSpace.homOfVector (𝔸(n; 𝔸(ULift.{u} (Fin 1); B)) ↘ _ ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B)
    fun i ↦ (𝔸(n; 𝔸(ULift.{u} (Fin 1); B)) ↘ _).appTop
      (AffineSpace.coord B (0 : ULift.{u} (Fin 1))) * AffineSpace.coord _ i

variable {n B}

/-- On the chart `Spec Γ(U)[t, I t⁻¹]` of the deformation space, the coordinate `t` of `𝔸¹_B` pulls
back to `t`. -/
lemma ι_deformationSpaceProj_appTop_coord {V : Scheme.{u}} (g : V ⟶ B) (s : B ⟶ V)
    (U : V.AffineZariskiSite) :
    (colimit.ι (relativeGluingData s.ker.coequifibered_toReesPresheaf).functor U ≫
      deformationSpaceProj g s).appTop (AffineSpace.coord B (0 : ULift.{u} (Fin 1))) =
      (ΓSpecIso (s.ker.reesPresheaf.obj (.op U))).inv
        ((s.ker.siteIdeal U).toExtendedReesAlgebra Polynomial.X) := by
  rw [deformationSpaceProj, IdealSheafData.deformationSpaceToPolynomialSpec,
    ι_relativeGluingMap_assoc, ι_polynomialSpecToAffineSpace_assoc, polynomialSpecChart,
    AffineSpace.homOfVector_map, AffineSpace.comp_homOfVector,
    AffineSpace.homOfVector_appTop_coord, Function.comp_apply,
    ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  rfl

/-- On the chart `Spec Γ(U)[t, I t⁻¹]` of the deformation space, a global function `a` of the base
pulls back to the constant `a|_U`. -/
lemma ι_deformationSpaceProj_appTop {V : Scheme.{u}} (I : V.IdealSheafData)
    (U : V.AffineZariskiSite) (a : Γ(V, ⊤)) :
    (colimit.ι (relativeGluingData I.coequifibered_toReesPresheaf).functor U ≫
      I.deformationSpaceProj).appTop a =
      (ΓSpecIso (I.reesPresheaf.obj (.op U))).inv
        (I.toReesPresheaf.app (.op U) (V.presheaf.map (homOfLE le_top).op a)) := by
  have h : colimit.ι (relativeGluingData I.coequifibered_toReesPresheaf).functor U ≫
      I.deformationSpaceProj = Spec.map (I.toReesPresheaf.app (.op U)) ≫ U.2.fromSpec := by
    rw [Cover.RelativeGluingData.ι_toBase]
    rfl
  have h' := U.2.fromSpec_app_of_le ⊤ le_top
  rw [h, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  simp only [Scheme.Hom.appTop]
  rw [h', CommRingCat.comp_apply, CommRingCat.comp_apply]
  simp only [← CommRingCat.comp_apply, Category.assoc]
  rw [Scheme.ΓSpecIso_inv_naturality]
  congr 3

variable (n B) in
/-- Under the identification `D_0 𝔸^n_B ≅ 𝔸^n_{𝔸¹_B}` of
`AlgebraicGeometry.Scheme.Hom.deformationSpaceToAffineSpace`, the projection `D_0 𝔸^n_B ⟶ 𝔸^n_B`
is the multiplication `(t, u) ↦ t u`: `x_k = t u_k`. -/
@[reassoc]
lemma deformationSpaceToAffineSpace_affineSpaceMul :
    deformationSpaceToAffineSpace n B ≫ affineSpaceMul n B =
      (AffineSpace.zeroSection n B).ker.deformationSpaceProj := by
  have hover : deformationSpaceToAffineSpace n B ≫ affineSpaceMul n B ≫ 𝔸(n; B) ↘ B =
      (AffineSpace.zeroSection n B).ker.deformationSpaceProj ≫ 𝔸(n; B) ↘ B := by
    rw [affineSpaceMul, AffineSpace.homOfVector_over, deformationSpaceToAffineSpace_over_assoc,
      deformationSpaceProj_over]
  refine colimit.hom_ext fun (U : (𝔸(n; B)).AffineZariskiSite) ↦
    AffineSpace.hom_ext ?_ fun i ↦ ?_
  · rw [Category.assoc, Category.assoc, hover, Category.assoc]
  · rw [ι_deformationSpaceToAffineSpace_assoc, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      affineSpaceMul, AffineSpace.homOfVector_appTop_coord, map_mul, ← CommRingCat.comp_apply,
      ← Scheme.Hom.comp_appTop, deformationSpaceToAffineSpaceChart, AffineSpace.homOfVector_over,
      AffineSpace.homOfVector_appTop_coord, ι_deformationSpaceProj_appTop_coord,
      ι_deformationSpaceProj_appTop]
    refine (map_mul _ _ _).symm.trans (congrArg _ ?_)
    apply Subtype.ext
    rw [Ideal.toExtendedReesAlgebra_X, MulMemClass.coe_mul, Ideal.coe_extendedReesAlgebraT, uCoord,
      mul_left_comm, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero, mul_one]
    rfl

variable (n) in
/-- Over an affine base `S`, the ideal of the zero section of `𝔸^n_S` is generated by the
coordinates on global sections. -/
lemma ideal_top_ker_zeroSection (S : Scheme.{u}) [IsAffine S] :
    (AffineSpace.zeroSection n S).ker.ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span (Set.range (AffineSpace.coord S)) := by
  have h := siteIdeal_affineOpenOver n S (isAffineOpen_top S)
  rw [Ideal.mvPolynomialOrigin, Ideal.map_span, ← Set.range_comp] at h
  refine h.trans ?_
  congr 2
  funext i
  rw [Function.comp_apply, polyToSections, MvPolynomial.eval₂Hom_X', AffineSpace.coordRes']
  exact congr($((𝔸(n; S)).presheaf.map_id _) (AffineSpace.coord S i))

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k']

/-- The affine line `𝔸¹_k = 𝔸(ULift (Fin 1); Spec k)`, as a `k`-scheme. -/
noncomputable abbrev affineLineOver : Over (Spec (.of k)) :=
  Over.mk (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))

/-- The identification `Spec k[x] ⟶ 𝔸(ULift (Fin 1); Spec k)` of the two models of the affine
line. -/
noncomputable def polyAffineOneHom :
    (polyAffine k 1).left ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) :=
  Spec.map (MvPolynomial.renameEquiv k Equiv.ulift).toRingEquiv.toCommRingCatIso.hom ≫
    (AffineSpace.SpecIso _ (.of k)).inv

instance : IsIso (polyAffineOneHom k) := by
  rw [polyAffineOneHom]
  infer_instance

/-- The identification `Spec k[x] ≅ 𝔸(ULift (Fin 1); Spec k)` of the two models of the affine
line. -/
noncomputable def polyAffineOneIso :
    (polyAffine k 1).left ≅ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) :=
  asIso (polyAffineOneHom k)

@[reassoc (attr := simp)]
lemma polyAffineOneIso_hom_over :
    (polyAffineOneIso k).hom ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k) =
      (polyAffine k 1).hom := by
  rw [polyAffineOneIso, asIso_hom, polyAffineOneHom, Category.assoc, AffineSpace.SpecIso_inv_over,
    ← Spec.map_comp]
  congr 1
  ext a
  simp

@[simp]
lemma polyAffineOneIso_hom_appTop_coord (i : ULift.{u} (Fin 1)) :
    (polyAffineOneIso k).hom.appTop (AffineSpace.coord _ i) = polyAffineCoord k (Fin.last 0) := by
  rw [polyAffineOneIso, asIso_hom, polyAffineOneHom, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, AffineSpace.SpecIso_inv_appTop_coord, ← CommRingCat.comp_apply,
    ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply, polyAffineCoord]
  congr 1
  simp [Subsingleton.elim i.down (Fin.last 0)]

/-- The identification of `Spec k[x]` with `𝔸(ULift (Fin 1); Spec k)`, as `k`-schemes. -/
noncomputable def polyAffineOneOverIso : polyAffine k 1 ≅ affineLineOver k :=
  Over.isoMk (polyAffineOneIso k) (polyAffineOneIso_hom_over k)

/-- The ideal `(x)` of the origin of `Spec k[x]` is the ideal of the zero section of
`𝔸(ULift (Fin 1); Spec k)`. -/
lemma polyAffineHyperplane_eq_comap :
    polyAffineHyperplane k 0 =
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k))).ker.comap
        (polyAffineOneIso k).hom := by
  refine IdealSheafData.ext_of_isAffine ?_
  rw [polyAffineHyperplane, IdealSheafData.ideal_top_ofIdealTop,
    IdealSheafData.ideal_top_comap_of_isAffine, Scheme.Hom.ideal_top_ker_zeroSection,
    Ideal.map_span, ← Set.range_comp]
  congr 1
  ext a
  simp only [Set.mem_singleton_iff, Set.mem_range, Function.comp_apply]
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact ⟨0, polyAffineOneIso_hom_appTop_coord k 0⟩
  · rintro ⟨i, rfl⟩
    exact polyAffineOneIso_hom_appTop_coord k i

/-- The ideal of the zero section of `𝔸¹_k` pulls back into the ideal `(x)` of `Spec k[x]`. -/
lemma siteIdeal_map_polyAffineOneIso_le ⦃U' : (polyAffine k 1).left.AffineZariskiSite⦄
    ⦃U : (𝔸(ULift.{u} (Fin 1); Spec (.of k))).AffineZariskiSite⦄
    (hU : U'.1 ≤ (polyAffineOneIso k).hom ⁻¹ᵁ U.1) :
    ((AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k))).ker.siteIdeal U).map
      ((polyAffineOneIso k).hom.appLE U.1 U'.1 hU).hom ≤
      (polyAffineHyperplane k 0).siteIdeal U' := by
  rw [polyAffineHyperplane_eq_comap]
  exact IdealSheafData.map_siteIdeal_le_comap _ _ hU

/-- The morphism `D_{(x)} Spec k[x] ⟶ D_0 𝔸¹_k` of deformation spaces induced by
`Spec k[x] ≅ 𝔸¹_k`. -/
noncomputable abbrev polyAffineDeformationSpaceMap :
    (polyAffineHyperplane k 0).deformationSpace ⟶
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k))).ker.deformationSpace :=
  IdealSheafData.deformationSpaceMap (polyAffineOneIso k).hom _ _
    (siteIdeal_map_polyAffineOneIso_le k)

instance : IsIso (polyAffineDeformationSpaceMap k) :=
  (IdealSheafData.isPullback_deformationSpaceMap_of_flat _ _ _ _
    (polyAffineHyperplane_eq_comap k)).isIso_fst_of_isIso

/-- The identification `D_{(x)} Spec k[x] ≅ 𝔸¹_{𝔸¹_k}` of the deformation space of the origin
of the affine line, with coordinates `(t, u)`, `x = t u`. -/
noncomputable def polyAffineDeformationSpaceToAffineSpace :
    (polyAffineHyperplane k 0).deformationSpace ⟶
      𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin 1); Spec (.of k))) :=
  polyAffineDeformationSpaceMap k ≫ Scheme.Hom.deformationSpaceToAffineSpace _ _

instance : IsIso (polyAffineDeformationSpaceToAffineSpace k) := by
  rw [polyAffineDeformationSpaceToAffineSpace]
  infer_instance

@[reassoc (attr := simp)]
lemma polyAffineDeformationSpaceToAffineSpace_over :
    polyAffineDeformationSpaceToAffineSpace k ≫
        𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin 1); Spec (.of k))) ↘ _ =
      deformationSpaceToAffineLine (polyAffine k 1) (polyAffineHyperplane k 0) := by
  rw [polyAffineDeformationSpaceToAffineSpace, Category.assoc,
    Scheme.Hom.deformationSpaceToAffineSpace_over]
  exact deformationSpaceMap_deformationSpaceToAffineLine (polyAffineOneOverIso k).hom
    (siteIdeal_map_polyAffineOneIso_le k)

@[reassoc]
lemma polyAffineDeformationSpaceToAffineSpace_affineSpaceMul :
    polyAffineDeformationSpaceToAffineSpace k ≫ Scheme.Hom.affineSpaceMul _ _ =
      (polyAffineHyperplane k 0).deformationSpaceProj ≫ (polyAffineOneIso k).hom := by
  rw [polyAffineDeformationSpaceToAffineSpace, Category.assoc,
    Scheme.Hom.deformationSpaceToAffineSpace_affineSpaceMul,
    IdealSheafData.deformationSpaceMap_toBase]

/-- The total space `𝒳` of the deformation to the normal cone of the origin of the affine line
over the trait is the base change of `𝔸¹_{𝔸¹_k} ⟶ 𝔸¹_k` along `t : S ⟶ 𝔸¹_k`. -/
lemma isPullback_deformationTotal_polyAffine :
    IsPullback (deformationTotalToSpace (polyAffine k 1) (polyAffineHyperplane k 0) k' ≫
        polyAffineDeformationSpaceToAffineSpace k)
      (deformationTotalToTrait (polyAffine k 1) (polyAffineHyperplane k 0) k')
      (𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin 1); Spec (.of k))) ↘ _) (traitToAffineLine k k') :=
  (isPullback_deformationTotal (polyAffine k 1) (polyAffineHyperplane k 0) k').of_iso
    (Iso.refl _) (asIso (polyAffineDeformationSpaceToAffineSpace k)) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

/-- **The deformation to the normal cone of the origin of the affine line over the trait is the
constant family**: `𝒳 ≅ 𝔸¹_S`, compatibly with the projections to `S = Spec k'⟦t⟧`. -/
noncomputable def deformationTotalPolyAffineIso :
    deformationTotal (polyAffine k 1) (polyAffineHyperplane k 0) k' ≅
      𝔸(ULift.{u} (Fin 1); trait k') :=
  (isPullback_deformationTotal_polyAffine k k').isoIsPullback _ _
    (AffineSpace.isPullback_map (traitToAffineLine k k'))

@[reassoc (attr := simp)]
lemma deformationTotalPolyAffineIso_hom_over :
    (deformationTotalPolyAffineIso k k').hom ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' =
      deformationTotalToTrait (polyAffine k 1) (polyAffineHyperplane k 0) k' :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

@[reassoc (attr := simp)]
lemma deformationTotalPolyAffineIso_inv_toTrait :
    (deformationTotalPolyAffineIso k k').inv ≫
        deformationTotalToTrait (polyAffine k 1) (polyAffineHyperplane k 0) k' =
      𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' :=
  IsPullback.isoIsPullback_inv_snd _ _ _ _

@[reassoc]
lemma deformationTotalPolyAffineIso_inv_toSpace :
    (deformationTotalPolyAffineIso k k').inv ≫
        deformationTotalToSpace (polyAffine k 1) (polyAffineHyperplane k 0) k' ≫
          polyAffineDeformationSpaceToAffineSpace k =
      AffineSpace.map _ (traitToAffineLine k k') :=
  IsPullback.isoIsPullback_inv_fst _ _ _ _

/-- **The identification `ε` is multiplication**: under `𝒳 ≅ 𝔸¹_S`
(`ProEtale.CondensedRing.deformationTotalPolyAffineIso`), the projection `𝒳 ⟶ 𝔸¹_k` is
`(u, t) ↦ t u`. -/
theorem deformationTotalPolyAffineIso_inv_toBase :
    (deformationTotalPolyAffineIso k k').inv ≫
        deformationTotalToBase (polyAffine k 1) (polyAffineHyperplane k 0) k' ≫
          (polyAffineOneIso k).hom =
      AffineSpace.homOfVector (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' ≫ traitToBase k k')
        fun i ↦ (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k').appTop
          ((ΓSpecIso (.of (PowerSeries k'))).inv PowerSeries.X) *
            AffineSpace.coord (trait k') i := by
  rw [deformationTotalToBase, Category.assoc,
    ← polyAffineDeformationSpaceToAffineSpace_affineSpaceMul,
    deformationTotalPolyAffineIso_inv_toSpace_assoc, Scheme.Hom.affineSpaceMul,
    AffineSpace.comp_homOfVector,
    AffineSpace.map_over_assoc, traitToAffineLine_over]
  congr 1
  funext i
  rw [Function.comp_apply, map_mul, AffineSpace.map_appTop_coord, ← CommRingCat.comp_apply,
    ← Scheme.Hom.comp_appTop, AffineSpace.map_over, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    traitToAffineLine, AffineSpace.homOfVector_appTop_coord]

/-- The coordinate `x` of `𝔸¹_k` pulls back to `t u` on `𝒳 ≅ 𝔸¹_S`. -/
lemma deformationTotalPolyAffineIso_inv_toBase_appTop :
    ((deformationTotalPolyAffineIso k k').inv ≫
        deformationTotalToBase (polyAffine k 1) (polyAffineHyperplane k 0) k').appTop
          (polyAffineCoord k (Fin.last 0)) =
      (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k').appTop
          ((ΓSpecIso (.of (PowerSeries k'))).inv PowerSeries.X) *
        AffineSpace.coord (trait k') 0 := by
  rw [← polyAffineOneIso_hom_appTop_coord k 0, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    Category.assoc, deformationTotalPolyAffineIso_inv_toBase, AffineSpace.homOfVector_appTop_coord]

end AlgebraicGeometry.ProEtale.CondensedRing
