/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraZero
public import WeilConjectures.CategoryTheory.Endofunctor.Shift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulated
public import WeilConjectures.TraceFormula.WeilDistTriangLowerShriek
public import WeilConjectures.TraceFormula.WeilDistTriangTrace

/-!

# Split triangles of Weil objects and the additivity of traces

For Weil objects `A`, `C` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for an endomorphism `Φ`, the direct sum `A ⊞ C`, with
the Frobenius structure `LΦ^*(A ⊞ C) ≅ LΦ^* A ⊞ LΦ^* C ≅ A ⊞ C`, sits in the split distinguished
triangle `A ⟶ A ⊞ C ⟶ C ⟶0 A[1]` of Weil objects. For a Weil object `A`, the rotated contractible
triangle `A ⟶ 0 ⟶ A[1] ⟶ A[1]` is a distinguished triangle of Weil objects. Consequently there are
Weil objects whose local and global traces are the sums of those of `A` and `C`, and Weil objects
whose local and global traces are the negatives of those of `A`.

## Main results

- `ProEtale.CondensedRing.WeilBoundedConstructible.isDistTriang_id_id`: the triangle
  `Z ⟶ Z ⟶ Z` of identities of a zero Weil object is distinguished.
- `ProEtale.CondensedRing.WeilBoundedConstructible.exists_isDistTriang_biprod`: every pair of
  Weil objects `A`, `C` sits in a distinguished triangle `A ⟶ B ⟶ C`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.exists_isDistTriang_isZero`: every Weil object
  `A` sits in a distinguished triangle `A ⟶ Z ⟶ C` with `Z` zero.
- `ProEtale.CondensedRing.weilStalkTraceAlternatingSum_eq_zero_of_isZero`,
  `weilStalkTraceAlternatingSum_weilCompactSupportCohomology_eq_zero_of_isZero`:
  the local and global traces of a zero Weil object vanish.
- `weilStalkTraceAlternatingSum_weilCompactSupportCohomology_eq_add_of_isDistTriang`:
  the global trace is additive along distinguished triangles of Weil objects.
- `ProEtale.CondensedRing.WeilBoundedConstructible.exists_weilStalkTraceAlternatingSum_eq_add`:
  the local and global traces of some Weil object are the sums of those of `A` and `C`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.exists_weilStalkTraceAlternatingSum_eq_neg`:
  the local and global traces of some Weil object are the negatives of those of `A`.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor Limits Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section ShiftConnecting

variable {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ C)
  (ι : C ⥤ D) (R : D ⥤ D) [F.CommShift ℤ] [ι.CommShift ℤ] [R.CommShift ℤ] (e : F ⋙ ι ≅ ι ⋙ R)
  [NatTrans.CommShift e.hom ℤ]

/-- For an algebra `(K, φ)` with invertible structure morphism of `F`, the structure morphism
`F (K[1]) ≅ (F K)[1] ≅ K[1]` of its shift is compatible, through the commutation
`c : ι (K[1]) ≅ (ι K)[1]`, with the connecting morphism transported along `e`
(`connectingOfIso`): the square
```
ι F (K[1]) ──ι φ_{K[1]}──▶ ι (K[1])
    │                          │
connectingOfIso c              c
    ▼                          ▼
(ι F K)[1] ───(ι φ)[1]────▶ (ι K)[1]
```
commutes. -/
lemma map_str_hom_comp_commShiftIso_hom_app_eq_connectingOfIso (K : IsoAlgebra F) :
    ι.map (IsoAlgebra.mk (K.carrier⟦(1 : ℤ)⟧) ((F.commShiftIso (1 : ℤ)).app K.carrier ≪≫
        (shiftFunctor C (1 : ℤ)).mapIso K.str)).str.hom ≫
        (ι.commShiftIso (1 : ℤ)).hom.app K.carrier =
      connectingOfIso F ι ι R e ((ι.commShiftIso (1 : ℤ)).hom.app K.carrier) ≫
        (shiftFunctor D (1 : ℤ)).map (ι.map K.str.hom) := by
  have h := connectingOfIso_map_comp_commShiftIso F ι ι R e (𝟙 (K.carrier⟦(1 : ℤ)⟧))
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h
  rw [h, Category.assoc, ← Functor.commShiftIso_hom_naturality, ← Functor.map_comp_assoc]
  rfl

end ShiftConnecting

section Existence

variable {V : Over (Spec (.of k))} [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
  [IsSeparated V.hom] {Φ : V ⟶ V}

/-- The triangle `Z ⟶ Z ⟶ Z` of identities of a zero Weil object is distinguished, with the zero
connecting morphism: it is isomorphic to the contractible triangle of the zero object. -/
theorem WeilBoundedConstructible.isDistTriang_id_id {Z : WeilBoundedConstructible ℓ Φ}
    (hZ : IsZero Z) : WeilBoundedConstructible.IsDistTriang ℓ (𝟙 Z) (𝟙 Z) := by
  have hZ₀ := (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
    V.left)).ι.map_isZero (IsoAlgebra.carrier_isZero hZ)
  have hZ₁ := (shiftFunctor (DerivedCategory _) (1 : ℤ)).map_isZero hZ₀
  refine ⟨0, ?_, hZ₁.eq_of_tgt _ _⟩
  refine isomorphic_distinguished _ (contractible_distinguished _) _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) hZ₀.isoZero ?_ ?_ ?_)
  · simp
  · exact (isZero_zero _).eq_of_tgt _ _
  · simp

/-- **Split triangles of Weil objects.** Two Weil objects `A` and `C` sit in a distinguished
triangle `A ⟶ B ⟶ C` of Weil objects: `B = A ⊞ C` with the Frobenius structure
`LΦ^*(A ⊞ C) ≅ LΦ^* A ⊞ LΦ^* C ≅ A ⊞ C`, the maps being the inclusion of `A` and the projection
to `C`, and the connecting morphism being zero. -/
theorem WeilBoundedConstructible.exists_isDistTriang_biprod (A C : WeilBoundedConstructible ℓ Φ) :
    ∃ (B : WeilBoundedConstructible ℓ Φ) (a : A ⟶ B) (b : B ⟶ C),
      WeilBoundedConstructible.IsDistTriang ℓ a b := by
  have := preservesBinaryBiproducts_of_preservesBiproducts
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ)
  have := preservesBinaryBiproducts_of_preservesBiproducts
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)).ι
  refine ⟨IsoAlgebra.mk (A.carrier ⊞ C.carrier)
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).mapBiprod A.carrier
      C.carrier ≪≫ biprod.mapIso A.str C.str),
    ObjectProperty.homMk ⟨biprod.inl, ?_⟩, ObjectProperty.homMk ⟨biprod.snd, ?_⟩, 0, ?_, ?_⟩
  · refine biprod.hom_ext _ _ ?_ ?_
    · simp only [IsoAlgebra.mk_obj, Iso.trans_hom, biprod.mapIso_hom, Functor.mapBiprod_hom,
        Category.assoc, biprod.map_fst, biprod.lift_fst_assoc, ← Functor.map_comp_assoc,
        biprod.inl_fst, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
        IsoAlgebra.str_hom]
    · simp only [IsoAlgebra.mk_obj, Iso.trans_hom, biprod.mapIso_hom, Functor.mapBiprod_hom,
        Category.assoc, biprod.map_snd, biprod.lift_snd_assoc, ← Functor.map_comp_assoc,
        biprod.inl_snd, Functor.map_zero, zero_comp, comp_zero]
  · simp only [IsoAlgebra.mk_obj, Iso.trans_hom, biprod.mapIso_hom, Functor.mapBiprod_hom,
      Category.assoc, biprod.map_snd, biprod.lift_snd_assoc, IsoAlgebra.str_hom]
  · refine isomorphic_distinguished _ (binaryBiproductTriangle_distinguished
      ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)).ι.obj
        A.carrier)
      ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)).ι.obj
        C.carrier)) _ (Triangle.isoMk _ _ (Iso.refl _)
      ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)).ι.mapBiprod
        A.carrier C.carrier) (Iso.refl _) ?_ ?_ ?_)
    · refine biprod.hom_ext _ _ ?_ ?_
      · simp only [Triangle.mk_mor₁, Iso.refl_hom, Category.id_comp,
          Category.assoc, Functor.mapBiprod_hom, biprod.lift_fst, ObjectProperty.homMk_hom,
          ← CategoryTheory.Functor.map_comp, biprod.inl_fst, CategoryTheory.Functor.map_id]
        exact biprod.inl_fst.symm
      · simp only [Triangle.mk_mor₁, Iso.refl_hom, Category.id_comp,
          Category.assoc, Functor.mapBiprod_hom, biprod.lift_snd, ObjectProperty.homMk_hom,
          ← CategoryTheory.Functor.map_comp, biprod.inl_snd, Functor.map_zero]
        exact biprod.inl_snd.symm
    · simp only [Triangle.mk_mor₂, binaryBiproductTriangle, Iso.refl_hom, Category.comp_id,
        Functor.mapBiprod_hom, ObjectProperty.homMk_hom]
      exact (biprod.lift_snd _ _).symm
    · simp
  · simp [connectingOfIso]

/-- **The rotated contractible triangle of a Weil object.** A Weil object `A` sits in a
distinguished triangle `A ⟶ Z ⟶ A[1] ⟶ A[1]` of Weil objects with `Z` zero, the connecting
morphism being the commutation of the inclusion `Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ D(Mod_{ℚ̲̄_ℓ,X})` with the
shift. -/
theorem WeilBoundedConstructible.exists_isDistTriang_isZero (A : WeilBoundedConstructible ℓ Φ) :
    ∃ (Z C : WeilBoundedConstructible ℓ Φ) (a : A ⟶ Z) (b : Z ⟶ C),
      IsZero Z ∧ WeilBoundedConstructible.IsDistTriang ℓ a b := by
  have hF := (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).map_isZero
    (isZero_zero (Dᵇc(V.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
  have hZ := (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
    V.left)).ι.map_isZero (isZero_zero (Dᵇc(V.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
  refine ⟨IsoAlgebra.mk 0 hF.isoZero, IsoAlgebra.mk (A.carrier⟦(1 : ℤ)⟧)
      (((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).commShiftIso
        (1 : ℤ)).app A.carrier ≪≫ (shiftFunctor _ (1 : ℤ)).mapIso A.str),
    ObjectProperty.homMk ⟨0, (isZero_zero _).eq_of_tgt _ _⟩,
    ObjectProperty.homMk ⟨0, hF.eq_of_src _ _⟩,
    IsoAlgebra.isZero_mk (isZero_zero _) _,
    ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)).ι.commShiftIso
      (1 : ℤ)).hom.app A.carrier, ?_, ?_⟩
  · refine isomorphic_distinguished _ (contractible_distinguished₂
      ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)).ι.obj
        A.carrier)) _ (Triangle.isoMk _ _ (Iso.refl _) hZ.isoZero
      (((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        V.left)).ι.commShiftIso (1 : ℤ)).app A.carrier) ?_ ?_ ?_)
    · exact (isZero_zero _).eq_of_tgt _ _
    · exact hZ.eq_of_src _ _
    · simp only [Triangle.mk_mor₃, Iso.refl_hom, Iso.app_hom, CategoryTheory.Functor.map_id]
      rfl
  · exact map_str_hom_comp_commShiftIso_hom_app_eq_connectingOfIso
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ)
      (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)).ι
      L((Φ.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
      (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ Φ) A

end Existence

section Trace

variable [Finite k] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- The local trace of a zero Weil object vanishes: by additivity along the distinguished
triangle `Z ⟶ Z ⟶ Z` of identities, `t(Z) = t(Z) + t(Z)`. -/
theorem weilStalkTraceAlternatingSum_eq_zero_of_isZero {e : X ≅ X} (n : ℕ)
    (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left)
    (hx : x ≫ (e.pow (n + 1)).hom.left = ((geometricFrobeniusField k).pow (n + 1)).hom ≫ x)
    {Z : WeilBoundedConstructible ℓ e.hom} (hZ : IsZero Z) :
    weilStalkTraceAlternatingSum ℓ (n + 1) x hx Z = 0 := by
  simpa using weilStalkTraceAlternatingSum_eq_add_of_isDistTriang ℓ n x hx
    (WeilBoundedConstructible.isDistTriang_id_id ℓ hZ)

/-- **Additivity of the global trace along distinguished triangles of Weil objects**: for a
distinguished triangle `A ⟶ B ⟶ C ⟶ A[1]` of Weil objects for `e`, the global traces of
`RΓ_c(X, -)` satisfy `L_{n+1}(X, B) = L_{n+1}(X, A) + L_{n+1}(X, C)`, the image under `Ra_!` of the
triangle being distinguished. -/
theorem weilStalkTraceAlternatingSum_weilCompactSupportCohomology_eq_add_of_isDistTriang
    (e : X ≅ X) (n : ℕ) {A B C : WeilBoundedConstructible ℓ e.hom} {a : A ⟶ B} {b : B ⟶ C}
    (h : WeilBoundedConstructible.IsDistTriang ℓ a b) :
    weilStalkTraceAlternatingSum ℓ (n + 1) (specAlgebraicClosure k)
        (specAlgebraicClosure_comp_pow (n + 1)) ((weilCompactSupportCohomology ℓ e).obj B) =
      weilStalkTraceAlternatingSum ℓ (n + 1) (specAlgebraicClosure k)
          (specAlgebraicClosure_comp_pow (n + 1)) ((weilCompactSupportCohomology ℓ e).obj A) +
        weilStalkTraceAlternatingSum ℓ (n + 1) (specAlgebraicClosure k)
          (specAlgebraicClosure_comp_pow (n + 1)) ((weilCompactSupportCohomology ℓ e).obj C) := by
  have h' := weilStalkTraceAlternatingSum_eq_add_of_isDistTriang ℓ n (specAlgebraicClosure k)
    (specAlgebraicClosure_comp_pow (n + 1))
    (WeilBoundedConstructible.IsDistTriang.weilLowerShriek_map ℓ e (Iso.refl (point k))
      (f := toPoint X) (toPoint_ext _ _) h)
  unfold weilCompactSupportCohomology
  exact h'

/-- The global trace of a zero Weil object vanishes: by additivity along the image under
`Ra_!` of the distinguished triangle `Z ⟶ Z ⟶ Z` of identities. -/
theorem weilStalkTraceAlternatingSum_weilCompactSupportCohomology_eq_zero_of_isZero
    (e : X ≅ X) (n : ℕ) {Z : WeilBoundedConstructible ℓ e.hom} (hZ : IsZero Z) :
    weilStalkTraceAlternatingSum ℓ (n + 1) (specAlgebraicClosure k)
      (specAlgebraicClosure_comp_pow (n + 1)) ((weilCompactSupportCohomology ℓ e).obj Z) = 0 := by
  simpa using weilStalkTraceAlternatingSum_weilCompactSupportCohomology_eq_add_of_isDistTriang ℓ
    e n (WeilBoundedConstructible.isDistTriang_id_id ℓ hZ)

/-- **Additivity of the traces on direct sums.** For Weil objects `A` and `C` there is a Weil
object `B` (the direct sum `A ⊞ C`) whose local traces at all points of degree `n + 1` and whose
global trace in degree `n + 1` are the sums of those of `A` and `C`. -/
theorem WeilBoundedConstructible.exists_weilStalkTraceAlternatingSum_eq_add (e : X ≅ X)
    (A C : WeilBoundedConstructible ℓ e.hom) :
    ∃ B : WeilBoundedConstructible ℓ e.hom,
      (∀ (n : ℕ) (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left)
        (hx : x ≫ (e.pow (n + 1)).hom.left = ((geometricFrobeniusField k).pow (n + 1)).hom ≫ x),
        weilStalkTraceAlternatingSum ℓ (n + 1) x hx B =
          weilStalkTraceAlternatingSum ℓ (n + 1) x hx A +
            weilStalkTraceAlternatingSum ℓ (n + 1) x hx C) ∧
      ∀ n : ℕ,
        weilStalkTraceAlternatingSum ℓ (n + 1) (specAlgebraicClosure k)
            (specAlgebraicClosure_comp_pow (n + 1)) ((weilCompactSupportCohomology ℓ e).obj B) =
          weilStalkTraceAlternatingSum ℓ (n + 1) (specAlgebraicClosure k)
              (specAlgebraicClosure_comp_pow (n + 1)) ((weilCompactSupportCohomology ℓ e).obj A) +
            weilStalkTraceAlternatingSum ℓ (n + 1) (specAlgebraicClosure k)
              (specAlgebraicClosure_comp_pow (n + 1))
                ((weilCompactSupportCohomology ℓ e).obj C) := by
  obtain ⟨B, a, b, h⟩ := WeilBoundedConstructible.exists_isDistTriang_biprod ℓ A C
  exact ⟨B, fun n x hx ↦ weilStalkTraceAlternatingSum_eq_add_of_isDistTriang ℓ n x hx h,
    fun n ↦ weilStalkTraceAlternatingSum_weilCompactSupportCohomology_eq_add_of_isDistTriang ℓ e
      n h⟩

/-- **The traces change sign under the shift.** For a Weil object `A` there is a Weil object `C`
(the shift `A[1]`) whose local traces at all points of degree `n + 1` and whose global trace in
degree `n + 1` are the negatives of those of `A`. -/
theorem WeilBoundedConstructible.exists_weilStalkTraceAlternatingSum_eq_neg (e : X ≅ X)
    (A : WeilBoundedConstructible ℓ e.hom) :
    ∃ C : WeilBoundedConstructible ℓ e.hom,
      (∀ (n : ℕ) (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left)
        (hx : x ≫ (e.pow (n + 1)).hom.left = ((geometricFrobeniusField k).pow (n + 1)).hom ≫ x),
        weilStalkTraceAlternatingSum ℓ (n + 1) x hx C =
          -weilStalkTraceAlternatingSum ℓ (n + 1) x hx A) ∧
      ∀ n : ℕ,
        weilStalkTraceAlternatingSum ℓ (n + 1) (specAlgebraicClosure k)
            (specAlgebraicClosure_comp_pow (n + 1)) ((weilCompactSupportCohomology ℓ e).obj C) =
          -weilStalkTraceAlternatingSum ℓ (n + 1) (specAlgebraicClosure k)
              (specAlgebraicClosure_comp_pow (n + 1))
                ((weilCompactSupportCohomology ℓ e).obj A) := by
  obtain ⟨Z, C, a, b, hZ, h⟩ := WeilBoundedConstructible.exists_isDistTriang_isZero ℓ A
  refine ⟨C, fun n x hx ↦ ?_, fun n ↦ ?_⟩
  · have h' := weilStalkTraceAlternatingSum_eq_add_of_isDistTriang ℓ n x hx h
    rw [weilStalkTraceAlternatingSum_eq_zero_of_isZero ℓ n x hx hZ] at h'
    exact eq_neg_of_add_eq_zero_right h'.symm
  · have h' :=
      weilStalkTraceAlternatingSum_weilCompactSupportCohomology_eq_add_of_isDistTriang ℓ e n h
    rw [weilStalkTraceAlternatingSum_weilCompactSupportCohomology_eq_zero_of_isZero ℓ e n hZ]
      at h'
    exact eq_neg_of_add_eq_zero_right h'.symm

end Trace

end AlgebraicGeometry.ProEtale.CondensedRing
