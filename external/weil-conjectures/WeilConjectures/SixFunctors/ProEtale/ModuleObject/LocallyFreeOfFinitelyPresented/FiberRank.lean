/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedMap
public import WeilConjectures.CategoryTheory.Preadditive.FinitePowerPivot
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented.Sections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-!
# Fibre ranks of finitely presented `ℚ̲̄_ℓ`-modules

Let `W` be a scheme and `N` a module object over `ℚ̲̄_ℓ,W`. We say that `N` has *fibre rank* `d`
at a point `x` of `W` (`ProEtale.CondensedRing.HasFiberRank`) if its pullback along
`Spec κ(x) ⟶ W` is free of rank `d`. Over `Spec κ(x)` the endomorphisms of the unit form the
field `ℚ̄_ℓ` (`ProEtale.CondensedRing.endRegularRingEquiv`, a point having a single point), so
the fibre rank is unique (`ProEtale.CondensedRing.HasFiberRank.unique`) and the cokernel of a
morphism `φ : (ℚ̲̄_ℓ,W)^m ⟶ (ℚ̲̄_ℓ,W)^n` has a fibre rank at every point
(`ProEtale.CondensedRing.exists_hasFiberRank_cokernel`).

A morphism `φ : (ℚ̲̄_ℓ,W)^m ⟶ (ℚ̲̄_ℓ,W)^n` is a matrix of sections of `ℚ̲̄_ℓ,W`; its pullback along
`g : W' ⟶ W` (`ProEtale.CondensedRing.upperStarFinFreeMap`) is the matrix of the restricted
sections (`ProEtale.CondensedRing.ι_upperStarFinFreeMap_π`). For `W` quasi-compact and
quasi-separated, the fibre rank of `coker φ` at `x` only depends on the matrix of values of the
entries of `φ` at `x`: it can be computed on any scheme with a single point over which the
residue field `κ(x)` lies (`ProEtale.CondensedRing.hasFiberRank_cokernel_of_endValue_eq`). It is
`n` exactly when all these values vanish
(`ProEtale.CondensedRing.hasFiberRank_cokernel_iff_endValue_eq_zero`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  {R : C} [MonObj R] [PreservesFiniteColimits (tensorLeft R)]

/-- The entry `(a, b)` of a morphism `φ : Rᵐ ⟶ Rⁿ` of free module objects: the endomorphism
`ι_b ≫ φ ≫ π_a` of the regular module `R`. -/
noncomputable def finFreeEntry {m n : ℕ} (φ : finiteFree R m ⟶ finiteFree R n) (a : Fin n)
    (b : Fin m) : End (regular R) :=
  .of (biproduct.ι (fun _ : Fin m ↦ regular R) b ≫ φ ≫
    biproduct.π (fun _ : Fin n ↦ regular R) a)

omit [PreservesFiniteColimits (tensorLeft R)] in
/-- A morphism of free module objects is determined by its entries. -/
lemma finFree_hom_ext {m n : ℕ} {φ ψ : finiteFree R m ⟶ finiteFree R n}
    (h : ∀ a b, finFreeEntry φ a b = finFreeEntry ψ a b) : φ = ψ :=
  biproduct_fin_hom_ext fun a b ↦ congr($(h a b).asHom)

omit [PreservesFiniteColimits (tensorLeft R)] in
@[simp]
lemma finFreeEntry_zero {m n : ℕ} (a : Fin n) (b : Fin m) :
    finFreeEntry (0 : finiteFree R m ⟶ finiteFree R n) a b = 0 := by
  apply End.ext
  simp [finFreeEntry]

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section General

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The pullback of the free module `(Λ_W)^d` along `g : W' ⟶ W` is `(Λ_{W'})^d`. -/
noncomputable def upperStarFiniteFreeIso {W' W : Scheme.{u}} (g : W' ⟶ W) (d : ℕ) :
    (g)^*⟦Λ⟧.obj (Mod.finiteFree (condensedRingObj Λ W) d) ≅
      Mod.finiteFree (condensedRingObj Λ W') d :=
  Mod.finiteFreeIsoMap _ (upperStarObjRegularIso Λ g) d

/-- The pullback along `g : W' ⟶ W` of a morphism `(Λ_W)^m ⟶ (Λ_W)^n`, as a morphism
`(Λ_{W'})^m ⟶ (Λ_{W'})^n`. -/
noncomputable def upperStarFinFreeMap {W' W : Scheme.{u}} (g : W' ⟶ W) {m n : ℕ}
    (φ : Mod.finiteFree (condensedRingObj Λ W) m ⟶ Mod.finiteFree (condensedRingObj Λ W) n) :
    Mod.finiteFree (condensedRingObj Λ W') m ⟶ Mod.finiteFree (condensedRingObj Λ W') n :=
  (upperStarFiniteFreeIso Λ g m).inv ≫ (g)^*⟦Λ⟧.map φ ≫ (upperStarFiniteFreeIso Λ g n).hom

/-- The cokernel of the pullback of `φ` is the pullback of the cokernel of `φ`. -/
noncomputable def cokernelUpperStarFinFreeMapIso {W' W : Scheme.{u}} (g : W' ⟶ W) {m n : ℕ}
    (φ : Mod.finiteFree (condensedRingObj Λ W) m ⟶ Mod.finiteFree (condensedRingObj Λ W) n) :
    cokernel (upperStarFinFreeMap Λ g φ) ≅ (g)^*⟦Λ⟧.obj (cokernel φ) :=
  (cokernel.mapIso _ _ (upperStarFiniteFreeIso Λ g m) (upperStarFiniteFreeIso Λ g n)
    (by simp [upperStarFinFreeMap])).symm ≪≫ (PreservesCokernel.iso _ φ).symm

/-- The entries of the pullback of `φ` are the restrictions of the entries of `φ`. -/
lemma ι_upperStarFinFreeMap_π {W' W : Scheme.{u}} (g : W' ⟶ W) {m n : ℕ}
    (φ : Mod.finiteFree (condensedRingObj Λ W) m ⟶ Mod.finiteFree (condensedRingObj Λ W) n)
    (a : Fin n) (b : Fin m) :
    Mod.finFreeEntry (upperStarFinFreeMap Λ g φ) a b =
      restrictEnd Λ g (Mod.finFreeEntry φ a b) := by
  apply End.ext
  simp [Mod.finFreeEntry, upperStarFinFreeMap, upperStarFiniteFreeIso, Mod.finiteFreeIsoMap,
    restrictEnd_apply]

end General

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- A module object `N` over `ℚ̲̄_ℓ,W` has *fibre rank* `d` at `x` if its pullback to the residue
field `Spec κ(x)` is free of rank `d`. -/
def HasFiberRank {W : Scheme.{u}}
    (N : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W)) (x : W) (d : ℕ) : Prop :=
  Nonempty ((W.fromSpecResidueField x)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj N ≅
    Mod.finiteFree _ d)

variable {ℓ}

lemma HasFiberRank.of_iso {W : Scheme.{u}}
    {N N' : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W)} (e : N ≅ N') {x : W} {d : ℕ}
    (h : HasFiberRank ℓ N x d) : HasFiberRank ℓ N' x d :=
  let ⟨e'⟩ := h
  ⟨(W.fromSpecResidueField x)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.mapIso e.symm ≪≫ e'⟩

/-- A free module of rank `d` has fibre rank `d` everywhere. -/
lemma hasFiberRank_finiteFree {W : Scheme.{u}} (x : W) (d : ℕ) :
    HasFiberRank ℓ (Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W) d)
      x d :=
  ⟨upperStarFiniteFreeIso _ _ d⟩

/-- Fibre ranks are compatible with pullback. -/
lemma HasFiberRank.upperStar {W' W : Scheme.{u}} (g : W' ⟶ W)
    {N : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W)} {x : W'} {d : ℕ}
    (h : HasFiberRank ℓ N (g x) d) :
    HasFiberRank ℓ ((g)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj N) x d := by
  obtain ⟨e⟩ := h
  exact ⟨((upperStarComp _ (W'.fromSpecResidueField x) g).app N).symm ≪≫
    (upperStarCongr _ (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g x).symm).app N ≪≫
    (upperStarComp _ _ _).app N ≪≫ (Spec.map (g.residueFieldMap x))^*⟦_⟧.mapIso e ≪≫
    upperStarFiniteFreeIso _ _ d⟩

/-- Over a scheme with exactly one point, the endomorphisms of the unit `ℚ̲̄_ℓ` form a field: a
nonzero endomorphism is invertible. -/
lemma isIso_of_ne_zero_residueField {W : Scheme.{u}} (x : W)
    (t : End (Mod.regular
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) (Spec (W.residueField x)))))
    (ht : t ≠ 0) : IsIso t.asHom :=
  isIso_of_ne_zero_of_subsingleton t ht

/-- **The fibre rank is unique.** -/
lemma HasFiberRank.unique {W : Scheme.{u}}
    {N : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W)} {x : W} {d d' : ℕ}
    (h : HasFiberRank ℓ N x d) (h' : HasFiberRank ℓ N x d') : d = d' := by
  obtain ⟨e⟩ := h
  obtain ⟨e'⟩ := h'
  obtain ⟨p⟩ : Nonempty (Spec (W.residueField x)) := inferInstance
  exact eq_of_iso_biproduct_fin (endValueRingHom p) (e.symm ≪≫ e')

/-- The cokernel of a morphism of finite free modules has a fibre rank at every point. -/
lemma exists_hasFiberRank_cokernel {W : Scheme.{u}} {m n : ℕ}
    (φ : Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W) m ⟶
      Mod.finiteFree _ n) (x : W) :
    ∃ d, HasFiberRank ℓ (cokernel φ) x d := by
  obtain ⟨d, -, -, ⟨e⟩⟩ := exists_le_iso_cokernel_biproduct_fin
    (isIso_of_ne_zero_residueField x) (upperStarFinFreeMap _ (W.fromSpecResidueField x) φ)
  exact ⟨d, ⟨(cokernelUpperStarFinFreeMapIso _ _ φ).symm ≪≫ e⟩⟩

/-- **The fibre rank only depends on the values of the matrix.** Let `φ : (ℚ̲̄_ℓ,W)^m ⟶ (ℚ̲̄_ℓ,W)^n`
and `ψ : (ℚ̲̄_ℓ,T)^m ⟶ (ℚ̲̄_ℓ,T)^n`, where `T` has a single point `t` and receives a morphism from
`Spec κ(x)`. If the entries of `φ` at `x` and of `ψ` at `t` have the same values and
`coker ψ ≅ (ℚ̲̄_ℓ,T)^d`, then `coker φ` has fibre rank `d` at `x`. -/
lemma hasFiberRank_cokernel_of_endValue_eq {W T : Scheme.{u}} [CompactSpace W]
    [QuasiSeparatedSpace W] [CompactSpace T] [QuasiSeparatedSpace T] [Subsingleton T] {m n : ℕ}
    (φ : Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W) m ⟶
      Mod.finiteFree _ n)
    (ψ : Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) T) m ⟶
      Mod.finiteFree _ n)
    (x : W) (t : T) (s : Spec (W.residueField x) ⟶ T)
    (h : ∀ a b, endValue ℓ (Mod.finFreeEntry φ a b) x =
      endValue ℓ (Mod.finFreeEntry ψ a b) t)
    {d : ℕ} (e : cokernel ψ ≅ Mod.finiteFree _ d) :
    HasFiberRank ℓ (cokernel φ) x d := by
  have heq : upperStarFinFreeMap _ (W.fromSpecResidueField x) φ = upperStarFinFreeMap _ s ψ := by
    refine Mod.finFree_hom_ext fun a b ↦ ?_
    rw [ι_upperStarFinFreeMap_π, ι_upperStarFinFreeMap_π]
    refine endValue_injective fun p ↦ ?_
    rw [endValue_restrictEnd, endValue_restrictEnd, fromSpecResidueField_apply, h a b,
      Subsingleton.elim (s p) t]
  exact ⟨(cokernelUpperStarFinFreeMapIso _ _ φ).symm ≪≫ cokernelIsoOfEq heq ≪≫
    cokernelUpperStarFinFreeMapIso _ s ψ ≪≫ (s)^*⟦_⟧.mapIso e ≪≫ upperStarFiniteFreeIso _ s d⟩

/-- The cokernel of `φ : (ℚ̲̄_ℓ,W)^m ⟶ (ℚ̲̄_ℓ,W)^n` has fibre rank `n` at `x` if and only if all the
entries of `φ` vanish at `x`. -/
lemma hasFiberRank_cokernel_iff_endValue_eq_zero {W : Scheme.{u}} [CompactSpace W]
    [QuasiSeparatedSpace W] {m n : ℕ}
    (φ : Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) W) m ⟶
      Mod.finiteFree _ n) (x : W) :
    HasFiberRank ℓ (cokernel φ) x n ↔
      ∀ a b, endValue ℓ (Mod.finFreeEntry φ a b) x = 0 := by
  have hval (a : Fin n) (b : Fin m) (p : Spec (W.residueField x)) :
      endValue ℓ (Mod.finFreeEntry (upperStarFinFreeMap _ (W.fromSpecResidueField x) φ) a b) p =
endValue ℓ (Mod.finFreeEntry φ a b) x := by
    rw [ι_upperStarFinFreeMap_π, endValue_restrictEnd, fromSpecResidueField_apply]
  obtain ⟨p⟩ : Nonempty (Spec (W.residueField x)) := inferInstance
  constructor
  · rintro ⟨e⟩ a b
    have h0 := eq_zero_of_cokernel_iso_biproduct_fin (isIso_of_ne_zero_residueField x)
      (endValueRingHom p) _ ((cokernelUpperStarFinFreeMapIso _ _ φ) ≪≫ e)
    rw [← hval a b p, h0, Mod.finFreeEntry_zero, ← endValueRingHom_apply, map_zero]
  · intro h
    have h0 : upperStarFinFreeMap _ (W.fromSpecResidueField x) φ = 0 :=
      Mod.finFree_hom_ext fun a b ↦ by
        rw [Mod.finFreeEntry_zero]
        exact eq_zero_of_forall_endValue_eq_zero fun q ↦ by rw [hval, h]
    exact ⟨(cokernelUpperStarFinFreeMapIso _ _ φ).symm ≪≫ cokernelIsoOfEq h0 ≪≫
      cokernelZeroIsoTarget⟩

end AlgebraicGeometry.ProEtale.CondensedRing
