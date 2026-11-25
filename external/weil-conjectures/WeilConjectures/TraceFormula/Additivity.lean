/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.RecollementTriangle
public import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersion
public import WeilConjectures.TraceFormula.ClosedPieceFrobenius
public import WeilConjectures.TraceFormula.OpenPieceFrobenius
import WeilConjectures.TraceFormula.CompactPullbackShift
import WeilConjectures.CategoryTheory.Monoidal.Rigid.BraidedTrace

/-!

# Additivity of the compactly supported Frobenius trace

Let `Φ` be a finite universal homeomorphism of `X`, `j : U ⟶ X` an open immersion and
`i : Z ⟶ X` a closed immersion onto the complement, both stable under `Φ`. For a Weil object
`(K, φ)` the trace of the compactly supported Frobenius on `RΓ_c(X, K)` is the sum of the traces
on `RΓ_c(U, K|_U)` and `RΓ_c(Z, K|_Z)` (blueprint `lemma-additivity-open-subscheme-complement`,
`lemma-additivity-open-subscheme-complement`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### The localization triangle -/

section Triangle

variable {X U Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left] (i : Z ⟶ X) [IsClosedImmersion i.left]

omit [IsClosedImmersion i.left] in
/-- The counit of `j_! ⊣ Lj^*` followed by the unit of `Li^* ⊣ Ri_*` vanishes, since
`Lj^* Ri_* = 0`. -/
lemma counit_comp_unit_eq_zero_of_isCompl
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j).counit.app K ≫
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K = 0 :=
  ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j).homEquiv _ _).injective
    ((isZero_boundedConstructibleUpperStar_obj_lowerStar_obj ℓ j i hcompl.disjoint _).eq_of_tgt
      _ _)

/-- The open–closed triangle `j_! Lj^* K ⟶ K ⟶ Ri_* Li^* K ⟶` with the extension by zero `j_!`:
the counit of `j_! ⊣ Lj^*` is inverted by `Lj^*`, which kills `Ri_* Li^* K`, and the unit of
`Li^* ⊣ Ri_*` is inverted by `Li^*`, which kills `j_! Lj^* K`; these restrictions jointly
reflect isomorphisms. -/
lemma exists_distTriang_openImmersionLowerShriek_openClosed
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∃ δ, Triangle.mk
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j).counit.app K))
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K)) δ ∈
      distTriang _ := by
  have : QuasiCompact (j.left ≫ X.hom) := by
    rw [Over.w j]
    infer_instance
  have : QuasiCompact j.left := QuasiCompact.of_comp j.left X.hom
  have hP := jointlyReflectIsomorphisms_leftDerivedUpperStar_of_isCompl
    (Profinite.padicAlgClRingObj ℓ) i.left j.left hcompl.symm
  have h₀ := counit_comp_unit_eq_zero_of_isCompl j i hcompl K
  have hzero : (boundedConstructible _).ι.map
      ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j).counit.app K) ≫
      (boundedConstructible _).ι.map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K) = 0 := by
    rw [← Functor.map_comp, h₀, Functor.map_zero]
  have h₁ : IsIso ((boundedConstructibleUpperStar _ ℓ j).map
      ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j).counit.app K)) :=
    IsIso.of_isIso_fac_left (hh := IsIso.id _)
      ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
        j).right_triangle_components K)
  have h₂ : IsIso ((boundedConstructibleUpperStar _ ℓ i).map
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K)) :=
    IsIso.of_isIso_fac_right (hh := IsIso.id _)
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).left_triangle_components K)
  have h₁' := (NatIso.isIso_map_iff (boundedConstructibleUpperStarCompatibility
    (Profinite.padicAlgClRingObj ℓ) ℓ j)
      ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j).counit.app K)).1
    (inferInstanceAs (IsIso ((boundedConstructible _).ι.map
      ((boundedConstructibleUpperStar _ ℓ j).map
        ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j).counit.app K)))))
  have h₂' := (NatIso.isIso_map_iff (boundedConstructibleUpperStarCompatibility
    (Profinite.padicAlgClRingObj ℓ) ℓ i)
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K)).1
    (inferInstanceAs (IsIso ((boundedConstructible _).ι.map
      ((boundedConstructibleUpperStar _ ℓ i).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K)))))
  have hN := ((boundedConstructible _).ι.map_isZero
    (isZero_boundedConstructibleUpperStar_obj_lowerStar_obj ℓ j i hcompl.disjoint
      ((boundedConstructibleUpperStar _ ℓ i).obj K))).of_iso
    ((boundedConstructibleUpperStarCompatibility _ ℓ j).symm.app _)
  have hA := ((boundedConstructible _).ι.map_isZero
    (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek _ ℓ j i
      hcompl.disjoint ((boundedConstructibleUpperStar _ ℓ j).obj K))).of_iso
    ((boundedConstructibleUpperStarCompatibility _ ℓ i).symm.app _)
  exact Pretriangulated.exists_distTriang_of_jointlyReflectIsomorphisms hP _ _ hzero h₁' hN hA h₂'

variable (ℓ) in
/-- **The open–closed localization triangle** (blueprint
`proposition-extension-zero-restriction-closed-subscheme--8`): for an open immersion `j : U ⟶ X` and
a closed immersion `i : Z ⟶ X` onto its complement, the counit `Rj_! Lj^* K ⟶ K` of `Rj_! ⊣ Lj^*`
and the unit `K ⟶ Ri_* Li^* K` of `Li^* ⊣ Ri_*` extend to a distinguished triangle
`Rj_! Lj^* K ⟶ K ⟶ Ri_* Li^* K ⟶ Rj_! Lj^* K[1]` of the ambient derived category
`D(Mod_{ℚ̲̄_ℓ,X})`. Through `Rj_! ≅ j_!`, this is
`exists_distTriang_openImmersionLowerShriek_openClosed`. -/
theorem exists_distTriang_openClosed
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∃ δ : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
          ((boundedConstructibleLowerStar ℓ i).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) ⟶
        (shiftFunctor _ (1 : ℤ)).obj
          ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
            ((boundedConstructibleLowerShriek ℓ j).obj
              ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))),
      Triangle.mk
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K))
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
            i).unit.app K)) δ ∈ distTriang _ := by
  obtain ⟨δ, hδ⟩ := exists_distTriang_openImmersionLowerShriek_openClosed j i hcompl K
  let γ := (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).app
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)
  have hε : (boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K =
      γ.hom ≫ (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ j).counit.app K :=
    counit_app_ofNatIsoRight_upperShriekIsoUpperStar ℓ j K
  refine ⟨δ ≫ (shiftFunctor _ (1 : ℤ)).map
    ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
      γ.inv), isomorphic_distinguished _ hδ _ ?_⟩
  refine Triangle.isoMk _ _
    ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.mapIso γ)
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · exact (Category.comp_id _).trans ((congrArg (boundedConstructible _).ι.map hε).trans
      (Functor.map_comp _ _ _))
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · refine (Category.assoc _ _ _).trans ((congrArg (δ ≫ ·) ?_).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm))
    rw [← Functor.map_comp, Functor.mapIso_hom, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]

end Triangle

/-! ### Transport of distinguished triangles along a comparison isomorphism -/

section Transport

variable {Cx Cs Dx Ds : Type*} [Category Cx] [Category Cs] [Category Dx] [Category Ds]
  [HasShift Dx ℤ] [HasShift Ds ℤ] (A : Cx ⥤ Cs) (ιs : Cs ⥤ Ds) (ι : Cx ⥤ Dx) (R : Dx ⥤ Ds)
  [R.CommShift ℤ] (e : A ⋙ ιs ≅ ι ⋙ R)

/-- For a comparison isomorphism `e : A ⋙ ι_s ≅ ι ⋙ R` with `R` commuting with the shifts, the
morphism `ι_s A c ⟶ (ι_s A a)[1]` corresponding to `δ : ι c ⟶ (ι a)[1]`. -/
noncomputable def connectingOfIso {a c : Cx}
    (δ : ι.obj c ⟶ (shiftFunctor Dx (1 : ℤ)).obj (ι.obj a)) :
    ιs.obj (A.obj c) ⟶ (shiftFunctor Ds (1 : ℤ)).obj (ιs.obj (A.obj a)) :=
  e.hom.app c ≫ R.map δ ≫ (R.commShiftIso (1 : ℤ)).hom.app (ι.obj a) ≫
    (shiftFunctor Ds (1 : ℤ)).map (e.inv.app a)

/-- If `Cx`, `Cs` carry shifts for which `ι`, `ι_s`, `A` and the comparison `e` commute with the
shifts, the morphism `connectingOfIso` attached to `ι δ₀` for `δ₀ : c ⟶ a⟦1⟧` is the image under
`ι_s` of `A δ₀` followed by the commutation of `A` with the shift:
```
ι_s A c ──e──▶ R ι c ──R (ι δ₀ ≫ comm)──▶ R ((ι a)⟦1⟧) ──comm──▶ (R ι a)⟦1⟧ ──e⁻¹⟦1⟧──▶ (ι_s A a)⟦1⟧
   ‖                                                                                       ‖
ι_s A c ─────────ι_s (A δ₀ ≫ comm)─────────▶ ι_s ((A a)⟦1⟧) ─────────comm─────────▶ (ι_s A a)⟦1⟧
```
-/
lemma connectingOfIso_map_comp_commShiftIso [HasShift Cx ℤ] [HasShift Cs ℤ] [A.CommShift ℤ]
    [ιs.CommShift ℤ] [ι.CommShift ℤ] [NatTrans.CommShift e.hom ℤ] {a c : Cx}
    (δ₀ : c ⟶ (shiftFunctor Cx (1 : ℤ)).obj a) :
    connectingOfIso A ιs ι R e (ι.map δ₀ ≫ (ι.commShiftIso (1 : ℤ)).hom.app a) =
      ιs.map (A.map δ₀ ≫ (A.commShiftIso (1 : ℤ)).hom.app a) ≫
        (ιs.commShiftIso (1 : ℤ)).hom.app (A.obj a) := by
  have h₁ := e.hom.naturality δ₀
  have h₂ := NatTrans.shift_app_comm e.hom (1 : ℤ) a
  simp only [Functor.comp_map, Functor.comp_obj, Functor.commShiftIso_comp_hom_app] at h₁ h₂
  simp only [connectingOfIso, Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₁.symm]
  slice_lhs 2 4 => rw [← h₂]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, Functor.comp_obj,
    CategoryTheory.Functor.map_id, Category.comp_id]

variable [HasZeroObject Dx] [HasZeroObject Ds] [Preadditive Dx] [Preadditive Ds]
  [∀ n : ℤ, (shiftFunctor Dx n).Additive] [∀ n : ℤ, (shiftFunctor Ds n).Additive]
  [Pretriangulated Dx] [Pretriangulated Ds] [R.IsTriangulated]

/-- The image under `A` of a triangle `a ⟶ b ⟶ c` of `Cx` which is distinguished through `ι` is
distinguished through `ι_s`, if `A` is compared with the triangulated functor `R`. -/
lemma distinguished_of_iso {a b c : Cx} {f : a ⟶ b} {g : b ⟶ c}
    {δ : ι.obj c ⟶ (shiftFunctor Dx (1 : ℤ)).obj (ι.obj a)}
    (h : Triangle.mk (ι.map f) (ι.map g) δ ∈ distTriang Dx) :
    Triangle.mk (ιs.map (A.map f)) (ιs.map (A.map g)) (connectingOfIso A ιs ι R e δ) ∈
      distTriang Ds :=
  isomorphic_distinguished _ (R.map_distinguished _ h) _
    (Triangle.isoMk _ _ (e.app a) (e.app b) (e.app c) (e.hom.naturality f) (e.hom.naturality g)
      (by
        simp only [connectingOfIso, Triangle.mk_mor₃, Iso.app_hom, Category.assoc,
          ← Functor.map_comp, Iso.inv_hom_id_app, Functor.comp_obj, CategoryTheory.Functor.map_id,
          Category.comp_id]
        rfl))

end Transport

/-! ### Squares with connecting morphisms -/

section ShiftSquares

variable {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]

/-- An identity between images of morphisms under a faithful functor `ι` commuting with the
shifts, composed with the commutation of `ι` with the shift, descends along `ι`: if the square
```
ι P ──ι a ≫ comm──▶ (ι Q)⟦1⟧
 ‖                     ▲
 ‖                (ι c)⟦1⟧
 ‖                     │
ι P ──ι b ≫ comm──▶ (ι Q')⟦1⟧
```
commutes, then `a = b ≫ c⟦1⟧`. -/
lemma eq_comp_shift_map_of_map_comp_commShiftIso (ι : C ⥤ D) [ι.Faithful] [ι.CommShift ℤ]
    {P Q Q' : C} (a : P ⟶ (shiftFunctor C (1 : ℤ)).obj Q)
    (b : P ⟶ (shiftFunctor C (1 : ℤ)).obj Q') (c : Q' ⟶ Q)
    (h : ι.map a ≫ (ι.commShiftIso (1 : ℤ)).hom.app Q =
      (ι.map b ≫ (ι.commShiftIso (1 : ℤ)).hom.app Q') ≫ (shiftFunctor D (1 : ℤ)).map (ι.map c)) :
    a = b ≫ (shiftFunctor C (1 : ℤ)).map c := by
  apply ι.map_injective
  rw [← cancel_mono ((ι.commShiftIso (1 : ℤ)).hom.app Q), h, Functor.map_comp, Category.assoc,
    Category.assoc, Functor.commShiftIso_hom_naturality]

/-- The image of a commutation with a shifted morphism under a functor `ι` commuting with the
shifts: if `x ≫ a = a ≫ y⟦1⟧`, then the square
```
ι P ──ι a ≫ comm──▶ (ι Q)⟦1⟧
 │                     │
ι x                (ι y)⟦1⟧
 ▼                     ▼
ι P ──ι a ≫ comm──▶ (ι Q)⟦1⟧
```
commutes. -/
lemma map_comp_commShiftIso_of_comp_eq (ι : C ⥤ D) [ι.CommShift ℤ] {P Q : C} (x : P ⟶ P)
    (y : Q ⟶ Q) (a : P ⟶ (shiftFunctor C (1 : ℤ)).obj Q)
    (h : x ≫ a = a ≫ (shiftFunctor C (1 : ℤ)).map y) :
    ι.map x ≫ ι.map a ≫ (ι.commShiftIso (1 : ℤ)).hom.app Q =
      (ι.map a ≫ (ι.commShiftIso (1 : ℤ)).hom.app Q) ≫ (shiftFunctor D (1 : ℤ)).map (ι.map y) := by
  rw [Category.assoc, ← Functor.commShiftIso_hom_naturality, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc, h]

/-- **The Frobenius operators commute with the connecting morphism**, abstractly: let
`θ : A ⟶ F ⋙ A` commute with the shifts, and let `ψ_Z : F M_Z ⟶ M_Z`, `ψ_U : F M_U ⟶ M_U`
commute with `δ₀ : M_Z ⟶ M_U⟦1⟧` through the commutation of `F` with the shift. Then
`E_Z = A ψ_Z ∘ θ` and `E_U = A ψ_U ∘ θ` commute with `A δ₀` followed by the commutation of `A`
with the shift:
```
A M_Z ──A δ₀ ≫ comm──▶ (A M_U)⟦1⟧
  │                        │
 E_Z                     E_U⟦1⟧
  ▼                        ▼
A M_Z ──A δ₀ ≫ comm──▶ (A M_U)⟦1⟧
```
-/
lemma comp_map_comp_commShiftIso_eq_of_commShift (A : C ⥤ D) (F : C ⥤ C) [A.CommShift ℤ]
    [F.CommShift ℤ] (θ : A ⟶ F ⋙ A) [NatTrans.CommShift θ ℤ] {MZ MU : C} (ψZ : F.obj MZ ⟶ MZ)
    (ψU : F.obj MU ⟶ MU) (δ₀ : MZ ⟶ (shiftFunctor C (1 : ℤ)).obj MU)
    (h : ψZ ≫ δ₀ = F.map δ₀ ≫ (F.commShiftIso (1 : ℤ)).hom.app MU ≫
      (shiftFunctor C (1 : ℤ)).map ψU) (EZ : A.obj MZ ⟶ A.obj MZ) (EU : A.obj MU ⟶ A.obj MU)
    (hZ : EZ = θ.app MZ ≫ A.map ψZ) (hU : EU = θ.app MU ≫ A.map ψU) :
    EZ ≫ A.map δ₀ ≫ (A.commShiftIso (1 : ℤ)).hom.app MU =
      (A.map δ₀ ≫ (A.commShiftIso (1 : ℤ)).hom.app MU) ≫ (shiftFunctor D (1 : ℤ)).map EU := by
  have hθ := NatTrans.shift_app_comm θ (1 : ℤ) MU
  have hn := θ.naturality δ₀
  rw [Functor.commShiftIso_comp_hom_app] at hθ
  simp only [Functor.comp_map] at hn
  rw [hZ, hU, Category.assoc, ← A.map_comp_assoc, h, Functor.map_comp, Functor.map_comp,
    Category.assoc, Category.assoc, Functor.commShiftIso_hom_naturality, reassoc_of% hn.symm,
    ← reassoc_of% hθ]
  simp only [Functor.map_comp, Category.assoc]

end ShiftSquares

/-! ### The compactly supported localization triangle -/

section CompactTriangle

variable {X U Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left] (i : Z ⟶ X)

variable (ℓ) in
/-- The connecting morphism `RΓ_c(X, Ri_* Li^* K) ⟶ RΓ_c(X, Rj_! Lj^* K)[1]` of the image under
`RΓ_c(X, -) = Ra_{X!}` of a localization triangle with connecting morphism `δ`, through the
ambient lower shriek, which is triangulated. -/
noncomputable def compactLocalizationConnecting
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (δ : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
          ((boundedConstructibleLowerStar ℓ i).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) ⟶
        (shiftFunctor _ (1 : ℤ)).obj
          ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
            ((boundedConstructibleLowerShriek ℓ j).obj
              ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)))) :
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (point k).left)).ι.obj
        ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj
          ((boundedConstructibleLowerStar ℓ i).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K))) ⟶
      (shiftFunctor _ (1 : ℤ)).obj
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (point k).left)).ι.obj
          ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj
            ((boundedConstructibleLowerShriek ℓ j).obj
              ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)))) :=
  haveI := HasCompactification.of_over (toPoint X)
  connectingOfIso (boundedConstructibleLowerShriek ℓ (toPoint X))
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (point k).left)).ι
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
    (R((toPoint X).left)_!⟦Profinite.padicAlgClRingObj ℓ⟧)
    (boundedConstructibleLowerShriekCompatibility ℓ (toPoint X))
    δ

variable (ℓ) in
/-- **The compactly supported localization triangle**: `RΓ_c(X, -)` of a localization triangle
`Rj_! Lj^* K ⟶ K ⟶ Ri_* Li^* K ⟶` is distinguished. -/
theorem compactLocalizationTriangle_distinguished
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (δ : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
          ((boundedConstructibleLowerStar ℓ i).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) ⟶
        (shiftFunctor _ (1 : ℤ)).obj
          ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
            ((boundedConstructibleLowerShriek ℓ j).obj
              ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))))
    (hδ : Triangle.mk
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K))
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
            i).unit.app K)) δ ∈ distTriang _) :
    Triangle.mk
      ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (point k).left)).ι.map
        ((boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K)))
      ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (point k).left)).ι.map
        ((boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
            i).unit.app K)))
      (compactLocalizationConnecting ℓ j i K δ) ∈ distTriang _ :=
  haveI := HasCompactification.of_over (toPoint X)
  distinguished_of_iso _ _ _ _ _ hδ

end CompactTriangle

/-! ### The Frobenius square with the connecting morphism on `X` -/

section ConnectingSquare

variable {X U Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  {j : U ⟶ X} [IsOpenImmersion j.left] {i : Z ⟶ X}
  {Φ : X ⟶ X} {ΦU : U ⟶ U} [IsUniversalHomeomorphism Φ.left] [IsUniversalHomeomorphism ΦU.left]

variable (ℓ) in
/-- No nonzero maps `(LΦ^* Rj_! N)[1] ⟶ Ri_* M` (blueprint
`lemma-additivity-open-subscheme-complement`, Step 2(c)): by the base change
`LΦ^* Rj_! ≅ Rj_! LΦ_U^*` along the cartesian square `Φ_U ≫ j = j ≫ Φ` and `Rj_! ≅ j_!`, the source
is a shifted extension by zero, and the range of `i` misses that of `j`. -/
lemma eq_zero_of_shift_upperStar_lowerShriek_to_lowerStar
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base)) (hj : ΦU ≫ j = j ≫ Φ)
    (N : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (M : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (d : (shiftFunctor _ (1 : ℤ)).obj
      ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj
          ((boundedConstructibleLowerShriek ℓ j).obj N))) ⟶
      (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
        ((boundedConstructibleLowerStar ℓ i).obj M)) :
    d = 0 := by
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
    (isPullback_of_comp_eq_of_isOpenImmersion j hj)
  let e := asIso ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
      (isPullback_of_comp_eq_of_isOpenImmersion j hj)).app N) ≪≫
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).app
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦU).obj N)
  rw [← cancel_mono ((boundedConstructibleLowerStarCompatibility
      ℓ i).hom.app M),
    ← cancel_epi ((shiftFunctor _ (1 : ℤ)).map
      ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
        e.inv)), zero_comp, comp_zero]
  exact eq_zero_of_shift_openImmersionLowerShriek_to_lowerStar _ ℓ j i hcompl.disjoint _ _ _ _

-- the triangles are compared through the inclusions of the bounded constructible categories
variable (ℓ) in
/-- **The Frobenius endomorphisms of the localization triangle commute with its connecting
morphism on `X`** (blueprint `lemma-additivity-open-subscheme-complement`, Step 2(c)): let
`ψ_U : LΦ^* Rj_! Lj^* K ⟶ Rj_! Lj^* K`, `φ : LΦ^* K ⟶ K` and `ψ_Z : LΦ^* Ri_* Li^* K ⟶ Ri_* Li^* K`
be compatible with the counit `ε` and the unit `η` of a localization triangle with connecting
morphism `δ`. Then `δ ∘ ψ_Z = ψ_U[1] ∘ LΦ^* δ`, where `LΦ^* δ` is formed through the ambient
derived pullback, which is triangulated: the third map of a morphism of triangles completing
`(ψ_U, φ)` is unique, there being no nonzero maps `(LΦ^* Rj_! Lj^* K)[1] ⟶ Ri_* Li^* K`. -/
theorem map_comp_connecting_eq_of_isCompl
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base)) (hj : ΦU ≫ j = j ≫ Φ)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (δ : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
          ((boundedConstructibleLowerStar ℓ i).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) ⟶
        (shiftFunctor _ (1 : ℤ)).obj
          ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
            ((boundedConstructibleLowerShriek ℓ j).obj
              ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))))
    (hδ : Triangle.mk
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K))
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
            i).unit.app K)) δ ∈ distTriang _)
    (ψU : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj
        ((boundedConstructibleLowerShriek ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)) ⟶
      (boundedConstructibleLowerShriek ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))
    (φ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K)
    (ψZ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj
        ((boundedConstructibleLowerStar ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) ⟶
      (boundedConstructibleLowerStar ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K))
    (ha : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).map
        ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K) ≫ φ =
      ψU ≫ (boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app K)
    (hb : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
          i).unit.app K) ≫ ψZ =
      φ ≫ (boundedConstructibleUpperStarLowerStarAdjunction ℓ
          i).unit.app K) :
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map ψZ ≫
        δ =
      connectingOfIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ)
          (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
          (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
          L((Φ.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
          (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ Φ) δ ≫
        (shiftFunctor _ (1 : ℤ)).map
          ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
            ψU) := by
  have hsub : Subsingleton ((shiftFunctor _ (1 : ℤ)).obj
      ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj
          ((boundedConstructibleLowerShriek ℓ j).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)))) ⟶
      (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
        ((boundedConstructibleLowerStar ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K))) :=
    ⟨fun a b ↦ (eq_zero_of_shift_upperStar_lowerShriek_to_lowerStar ℓ hcompl hj _ _ a).trans
      (eq_zero_of_shift_upperStar_lowerShriek_to_lowerStar ℓ hcompl hj _ _ b).symm⟩
  have hT := distinguished_of_iso
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ)
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
    L((Φ.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
    (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ Φ) hδ
  obtain ⟨τ, -, -, -, h⟩ := ((triangle_morphism_extension _ _ hT hδ
    ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
      φ)).2.1 hsub).2.2
    ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map ψU)
    ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map ψZ)
    (by simp only [Triangle.mk_mor₁, ← Functor.map_comp, ha])
    (by simp only [Triangle.mk_mor₂, ← Functor.map_comp, hb])
  exact h.symm

end ConnectingSquare

/-! ### Triangle additivity of the trace -/

attribute [local instance] boundedConstructibleBraiding

/-- **Triangle additivity of the trace** (blueprint `proposition-properties-trace`, item (2)): for
a distinguished triangle `P₁ ⟶ P₂ ⟶ P₃ ⟶ P₁[1]` of dualizable objects of `Dᵇc(s)⟦ℚ̲̄_ℓ⟧` (through
the inclusion into `D(Mod_{ℚ̲̄_ℓ,s})`) and an endomorphism `(v₁, v₂, v₃)` of it,
`tr v₂ = tr v₁ + tr v₃`. Over the field `ℚ̄_ℓ` the filtered origin required in item (2) is
automatic: by item (4) the trace is the alternating sum of the traces on the cohomology, which is
additive along the long exact cohomology sequence of an endomorphism of a triangle. -/
theorem trace_eq_trace_add_trace_of_distTriang [IsSepClosed k]
    {P₁ P₂ P₃ : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧} [HasRightDual P₁]
    [HasRightDual P₂] [HasRightDual P₃] (f : P₁ ⟶ P₂) (g : P₂ ⟶ P₃)
    (δ : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (point k).left)).ι.obj P₃ ⟶
      (shiftFunctor _ (1 : ℤ)).obj
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (point k).left)).ι.obj P₁))
    (hT : Triangle.mk
      ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (point k).left)).ι.map f)
      ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (point k).left)).ι.map g) δ ∈ distTriang _)
    (v₁ : P₁ ⟶ P₁) (v₂ : P₂ ⟶ P₂) (v₃ : P₃ ⟶ P₃) (h₁ : v₁ ≫ f = f ≫ v₂)
    (h₂ : v₂ ≫ g = g ≫ v₃)
    (h₃ : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (point k).left)).ι.map v₃ ≫ δ =
      δ ≫ (shiftFunctor _ (1 : ℤ)).map
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (point k).left)).ι.map v₁)) :
    trace v₂ = trace v₁ + trace v₃ := by
  let ι := (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
    (point k).left)).ι
  let := DerivedCategory.braidedCategory' (PointMod ℓ k)
  let : HasRightDual (ι.obj P₁) :=
    @HasRightDual.mk _ _ _ _ (ι.obj (P₁ᘁ)) (ExactPairing.map ι P₁ (P₁ᘁ))
  let : HasRightDual (ι.obj P₂) :=
    @HasRightDual.mk _ _ _ _ (ι.obj (P₂ᘁ)) (ExactPairing.map ι P₂ (P₂ᘁ))
  let : HasRightDual (ι.obj P₃) :=
    @HasRightDual.mk _ _ _ _ (ι.obj (P₃ᘁ)) (ExactPairing.map ι P₃ (P₃ᘁ))
  have key {P : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧} [HasRightDual P]
      [HasRightDual (ι.obj P)] (v : P ⟶ P) :
      trace (ι.map v) = (ι.unitEndRingHom (.of (trace v))).asHom :=
    ι.trace_eq_unitEndRingHom_trace v (ι.map v) (Iso.refl _) (by simp)
  have hinj : Function.Injective ι.unitEndRingHom := fun a b h ↦ by
    rw [Functor.unitEndRingHom_apply, Functor.unitEndRingHom_apply] at h
    apply End.ext
    apply ι.map_injective
    have h := congrArg End.asHom h
    change 𝟙 _ ≫ ι.map a.asHom ≫ 𝟙 _ = 𝟙 _ ≫ ι.map b.asHom ≫ 𝟙 _ at h
    simpa only [Category.id_comp, Category.comp_id] using h
  suffices h : End.of (trace v₂) = End.of (trace v₁) + End.of (trace v₃) from
    congrArg End.asHom h
  apply hinj
  apply End.ext
  rw [RingHom.map_add, End.add_asHom, ← key, ← key, ← key]
  exact trace_eq_trace_add_trace_of_distTriang_of_shiftDecomposition ℓ k
    ((nonempty_shiftDecomposition_point ℓ k P₁).some.map ι)
    ((nonempty_shiftDecomposition_point ℓ k P₂).some.map ι)
    ((nonempty_shiftDecomposition_point ℓ k P₃).some.map ι) (ι.map f) (ι.map g) δ hT
    (ι.map v₁) (ι.map v₂) (ι.map v₃) (by rw [← ι.map_comp, ← ι.map_comp, h₁])
    (by rw [← ι.map_comp, ← ι.map_comp, h₂]) h₃

section Frobenius

variable {X U Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

variable {Φ : X ⟶ X} {ΦU : U ⟶ U} {ΦZ : Z ⟶ Z} {j : U ⟶ X} {i : Z ⟶ X}
  [IsOpenImmersion j.left] [IsClosedImmersion i.left] [IsFinite Φ.left]
  [IsUniversalHomeomorphism Φ.left] [IsFinite ΦU.left] [IsUniversalHomeomorphism ΦU.left]
  [IsFinite ΦZ.left] [IsUniversalHomeomorphism ΦZ.left]

namespace WeilBoundedConstructible

/-- The image under `ι` of `δ₀` followed by the commutation of `ι` with the shift. -/
lemma exists_eq_map_comp_commShiftIso {C D : Type*} [Category C] [Category D] [HasShift C ℤ]
    [HasShift D ℤ] {ι : C ⥤ D} (hι : ι.FullyFaithful) [ι.CommShift ℤ] {a c : C}
    (δ : ι.obj c ⟶ (shiftFunctor D (1 : ℤ)).obj (ι.obj a)) :
    ∃ δ₀ : c ⟶ (shiftFunctor C (1 : ℤ)).obj a,
      δ = ι.map δ₀ ≫ (ι.commShiftIso (1 : ℤ)).hom.app a :=
  ⟨hι.preimage (δ ≫ (ι.commShiftIso (1 : ℤ)).inv.app a), by simp⟩

variable (ℓ) in
omit [IsUniversalHomeomorphism ΦZ.left] in
/-- **The operators `E_Z`, `E_U` commute with the connecting morphism of the compactly supported
localization triangle** (blueprint `lemma-additivity-open-subscheme-complement`, Step 3). Write
`E_Z = RΓ_c(ψ_Z) ∘ Φ^♯` and `E_U = RΓ_c(ψ_U) ∘ Φ^♯` (`compactFrobeniusClosedPiece_eq`,
`compactFrobeniusOpenPiece_eq`) with Frobenius coefficients `ψ_Z`, `ψ_U` compatible with the unit
and counit of the localization triangle. By Hom vanishing these commute with the connecting
morphism `δ` on `X` (`map_comp_connecting_eq_of_isCompl`), and `Φ^♯` commutes with the shifts
(`commShift_compactPullback`). -/
theorem compactFrobenius_connecting_compat
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (hj : ΦU ≫ j = j ≫ Φ) (hi : ΦZ ≫ i = i ≫ Φ) (K : WeilBoundedConstructible ℓ Φ)
    (δ : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
          ((boundedConstructibleLowerStar ℓ i).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)) ⟶
        (shiftFunctor _ (1 : ℤ)).obj
          ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.obj
            ((boundedConstructibleLowerShriek ℓ j).obj
              ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
                K.carrier))))
    (hδ : Triangle.mk
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ j).counit.app
            K.carrier))
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι.map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
            i).unit.app K.carrier)) δ ∈ distTriang _) :
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (point k).left)).ι.map (compactFrobeniusClosedPiece ℓ hi K) ≫
        compactLocalizationConnecting ℓ j i K.carrier δ =
      compactLocalizationConnecting ℓ j i K.carrier δ ≫ (shiftFunctor _ (1 : ℤ)).map
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (point k).left)).ι.map (compactFrobeniusOpenPiece ℓ hj K)) := by
  have hX := map_comp_connecting_eq_of_isCompl ℓ hcompl hj K.carrier δ hδ
    (openPieceFrobeniusCoeff ℓ hj K) K.str.hom (closedPieceFrobeniusCoeff ℓ hi K)
    (upperStar_map_counit_comp_str_hom hj K)
    (upperStar_map_unit_comp_closedPieceFrobeniusCoeff hi K)
  obtain ⟨δ₀, rfl⟩ := exists_eq_map_comp_commShiftIso
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).fullyFaithfulι
    δ
  rw [connectingOfIso_map_comp_commShiftIso, ← Functor.map_comp_assoc] at hX
  have key₁ := eq_comp_shift_map_of_map_comp_commShiftIso _ _ _ _ hX
  have key₂ := comp_map_comp_commShiftIso_eq_of_commShift
    (boundedConstructibleLowerShriek ℓ (toPoint X))
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ) (compactPullback ℓ Φ)
    (closedPieceFrobeniusCoeff ℓ hi K) (openPieceFrobeniusCoeff ℓ hj K) δ₀
    (key₁.trans (Category.assoc _ _ _))
    (compactFrobeniusClosedPiece ℓ hi K) (compactFrobeniusOpenPiece ℓ hj K)
    (compactFrobeniusClosedPiece_eq hi K) (compactFrobeniusOpenPiece_eq hj K)
  have := HasCompactification.of_over (toPoint X)
  rw [compactLocalizationConnecting, connectingOfIso_map_comp_commShiftIso]
  exact map_comp_commShiftIso_of_comp_eq _ _ _ _ key₂

/-- **Additivity of the compactly supported Frobenius along an open–closed decomposition**
(blueprint `lemma-additivity-open-subscheme-complement`): for an open
immersion `j : U ⟶ X` with closed complement `i : Z ⟶ X`, both stable under the Frobenius,
`tr(F_c | RΓ_c(X, K)) = tr(F_c | RΓ_c(U, K|_U)) + tr(F_c | RΓ_c(Z, K|_Z))`. -/
theorem trace_compactFrobenius_eq_add_of_isCompl [IsSepClosed k]
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (hj : ΦU ≫ j = j ≫ Φ) (hi : ΦZ ≫ i = i ≫ Φ) (K : WeilBoundedConstructible ℓ Φ)
    [HasRightDual
      ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        K.carrier)]
    [hU : HasRightDual
      ((boundedConstructibleLowerShriek ℓ (toPoint U)).obj
        ((weilUpperStar ℓ ΦU Φ j hj).obj K).carrier)]
    [hZ : HasRightDual
      ((boundedConstructibleLowerShriek ℓ (toPoint Z)).obj
        ((weilUpperStar ℓ ΦZ Φ i hi).obj K).carrier)] :
    trace K.compactFrobenius =
      trace ((weilUpperStar ℓ ΦU Φ j hj).obj K).compactFrobenius +
        trace ((weilUpperStar ℓ ΦZ Φ i hi).obj K).compactFrobenius := by
  obtain ⟨δ, hδ⟩ := exists_distTriang_openClosed ℓ j i hcompl K.carrier
  have h₁ := compactFrobeniusOpenPiece_comp_counit hj K
  have h₃ := compactFrobenius_connecting_compat ℓ hcompl hj hi K δ hδ
  let : HasRightDual
      ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        ((boundedConstructibleLowerShriek ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
            K.carrier))) :=
    @hasRightDualOfIso _ _ _ _ _ ((boundedConstructibleLowerShriekCompToPoint ℓ j).app
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier)) hU
  let : HasRightDual
      ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        ((boundedConstructibleLowerStar ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj
            K.carrier))) :=
    @hasRightDualOfIso _ _ _ _ _ ((boundedConstructibleLowerStarCompToPoint ℓ i).app
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)) hZ
  let : HasRightDual
      ((boundedConstructibleLowerShriek ℓ (toPoint U)).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier)) := hU
  let : HasRightDual
      ((boundedConstructibleLowerShriek ℓ (toPoint Z)).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)) := hZ
  have hT := compactLocalizationTriangle_distinguished ℓ j i K.carrier δ hδ
  have h₂ := compactFrobenius_comp_compactUnit hi K
  dsimp only [Functor.comp_obj, Functor.id_obj] at hT h₁ h₂ h₃
  rw [trace_eq_trace_add_trace_of_distTriang _ _ _ hT _ _ _ h₁ h₂ h₃]
  congr 1
  · let w : (boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        ((boundedConstructibleLowerShriek ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier)) ≅
        (boundedConstructibleLowerShriek ℓ (toPoint U)).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier) :=
      (boundedConstructibleLowerShriekCompToPoint ℓ j).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K.carrier)
    refine trace_eq_of_iso w _ _ ?_
    simp only [w, compactFrobeniusOpenPiece, Iso.app_hom, Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
  · let w : (boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        ((boundedConstructibleLowerStar ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)) ≅
        (boundedConstructibleLowerShriek ℓ (toPoint Z)).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier) :=
      (boundedConstructibleLowerStarCompToPoint ℓ i).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)
    refine trace_eq_of_iso w _ _ ?_
    rw [compactFrobenius_weilUpperStar hi K]
    simp only [w, compactFrobeniusClosedPiece, Iso.app_hom, Category.assoc, Iso.inv_hom_id_app,
      Category.comp_id]

end WeilBoundedConstructible

end Frobenius

end AlgebraicGeometry.ProEtale.CondensedRing
