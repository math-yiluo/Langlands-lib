/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ZModPowAbSheafCokernel
public import Mathlib.Data.ZMod.Units
public import WeilConjectures.SixFunctors.ProEtale.Adic.ProEtOpenCover

/-!
# Automorphisms of `(ℤ/ℓⁿ)_X` lift to `(ℤ/ℓⁿ⁺¹)_X`

Let `Y` be an object of `X_proét` and `m : ℕ`. A morphism of abelian sheaves out of the
restriction `(ℤ/m)|_Y` of the sheaf of locally constant functions `C(-, ℤ/m)` is determined by
the image of the global section `1` (`AlgebraicGeometry.ProEtale.zmodAbSheafOver_hom_ext`): a
section `s` is, on the open cover by its fibres `s⁻¹(k)`, the multiple `k • 1`. Hence every
endomorphism of `(ℤ/m)|_Y` is the multiplication by a locally constant function
`c : Y → ℤ/m` (`AlgebraicGeometry.ProEtale.zmodAbSheafOverMul`), and the automorphisms are the
multiplications by pointwise units.

A pointwise unit `u : Y → ℤ/ℓⁿ` lifts pointwise to a unit `Y → ℤ/ℓⁿ⁺¹`, continuously since
`ℤ/ℓⁿ` is discrete. Therefore every automorphism of `(ℤ/ℓⁿ)|_Y` lifts to an automorphism of
`(ℤ/ℓⁿ⁺¹)|_Y` along the reduction
(`AlgebraicGeometry.ProEtale.exists_iso_hom_comp_zmodPowAbSheafDiagram_map`), and an `ℓ`-adic
tower `(Gₙ)` of abelian sheaves with each `Gₙ` locally isomorphic to `(ℤ/ℓⁿ)_X` has a limit which
is locally isomorphic to `ℤ_ℓ,X`
(`AlgebraicGeometry.ProEtale.exists_cover_nonempty_iso_padicIntAbSheaf_of_locally_iso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X : Scheme.{u}}

/-- The restriction `(ℤ/m)|_Y` to an object `Y` of `X_proét` of the abelian sheaf `C(-, ℤ/m)` of
locally constant functions. -/
noncomputable abbrev zmodAbSheafOver (m : ℕ) (Y : X.ProEt) :
    Sheaf ((ProEt.topology X).over Y) Ab.{u + 1} :=
  ((ProEt.topology X).overPullback Ab.{u + 1} Y).obj
    ((sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (continuousMapRingSheaf X (ZMod m)))

/-- The section of `(ℤ/m)|_Y` over `U` given by a locally constant function `U → ℤ/m`. -/
noncomputable abbrev zmodAbSheafOver.mk {m : ℕ} {Y : X.ProEt} (U : Over Y)
    (c : C(U.left.left, ZMod m)) : (zmodAbSheafOver m Y).obj.obj (op U) :=
  ULift.up c

/-- Multiplication by a locally constant function `c : Y → ℤ/m`, as an endomorphism of the
abelian sheaf `(ℤ/m)|_Y`. -/
noncomputable def zmodAbSheafOverMul {m : ℕ} {Y : X.ProEt} (c : C(Y.left, ZMod m)) :
    zmodAbSheafOver m Y ⟶ zmodAbSheafOver m Y :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom (AddMonoidHom.mulLeft
        (ULift.up (c.comp U.unop.hom.left.base.hom) : ULift.{u + 1} C(U.unop.left.left, ZMod m)))
      naturality U V φ := by
        ext s
        refine ULift.ext (ContinuousMap.ext fun t ↦ ?_)
        have h : V.unop.hom.left.base t = U.unop.hom.left.base (φ.unop.left.left.base t) := by
          rw [← Over.w φ.unop]
          rfl
        exact congrArg (· * s.down (φ.unop.left.left.base t)) (congrArg c h) }

/-- `Over.mk (𝟙 Y)` is the terminal object of `Over Y`; the morphism to it from `U`. -/
abbrev Over.toMkId {Y : X.ProEt} (U : Over Y) : U ⟶ Over.mk (𝟙 Y) :=
  Over.homMk U.hom (Category.comp_id _)

/-- **Morphisms out of `(ℤ/m)|_Y` are determined by the image of `1`**: a section `s` over `U` is,
on the open cover of `U` by the fibres `s⁻¹(k)`, the multiple `k • 1` of the restriction of the
global section `1`. -/
lemma zmodAbSheafOver_hom_ext {m : ℕ} {Y : X.ProEt}
    {F : Sheaf ((ProEt.topology X).over Y) Ab.{u + 1}} {f g : zmodAbSheafOver m Y ⟶ F}
    (h : f.hom.app (op (Over.mk (𝟙 Y))) (zmodAbSheafOver.mk _ 1) =
      g.hom.app (op (Over.mk (𝟙 Y))) (zmodAbSheafOver.mk _ 1)) : f = g := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U ↦ ?_))
  ext s
  have hF := (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget Ab.{u + 1})).1 F.property)
  let W (k : ZMod m) : U.unop.left.left.Opens :=
    ⟨s.down ⁻¹' {k}, (isOpen_discrete _).preimage s.down.continuous⟩
  refine (hF _ (GrothendieckTopology.overEquiv_symm_mem_over _ _ _
    (ProEt.generate_ofArrows_mem_topology U.unop.left W fun x ↦ ⟨s.down x, rfl⟩))
    ).isSeparatedFor.ext
    fun Z φ hφ ↦ ?_
  rw [Sieve.overEquiv_symm_iff] at hφ
  obtain ⟨V, a, b, hb, hab⟩ := hφ
  rcases hb with ⟨k⟩
  have hs : (zmodAbSheafOver m _).obj.map φ.op s =
      (ZMod.cast k : ℤ) •
        (zmodAbSheafOver m _).obj.map (Over.toMkId Z).op (zmodAbSheafOver.mk _ 1) := by
    refine ULift.ext (ContinuousMap.ext fun t ↦ ?_)
    have ht : φ.left.left.base t ∈ W k := by
      rw [← hab]
      exact (a.left t).2
    refine (ht : s.down (φ.left.left.base t) = k).trans ?_
    exact (by rw [zsmul_eq_mul, mul_one, ZMod.intCast_zmod_cast] :
      k = (ZMod.cast k : ℤ) • (1 : ZMod m))
  calc (F.obj ⋙ forget Ab.{u + 1}).map φ.op (f.hom.app U s)
      = f.hom.app _ ((zmodAbSheafOver m _).obj.map φ.op s) :=
        (NatTrans.naturality_apply f.hom φ.op s).symm
    _ = (ZMod.cast k : ℤ) • F.obj.map (Over.toMkId Z).op
          (f.hom.app _ (zmodAbSheafOver.mk _ 1)) := by
        rw [hs, map_zsmul, NatTrans.naturality_apply]
    _ = (ZMod.cast k : ℤ) • F.obj.map (Over.toMkId Z).op
          (g.hom.app _ (zmodAbSheafOver.mk _ 1)) := by
        rw [h]
    _ = (F.obj ⋙ forget Ab.{u + 1}).map φ.op (g.hom.app U s) := by
        rw [← NatTrans.naturality_apply, ← map_zsmul, ← hs]
        exact NatTrans.naturality_apply g.hom φ.op s

/-- On global sections, multiplication by `c` is the multiplication by `c`. -/
lemma zmodAbSheafOverMul_app_mkId {m : ℕ} {Y : X.ProEt} (c : C(Y.left, ZMod m))
    (x : C(Y.left, ZMod m)) :
    (zmodAbSheafOverMul c).hom.app (op (Over.mk (𝟙 Y))) (zmodAbSheafOver.mk _ x) =
      zmodAbSheafOver.mk _ (c * x) :=
  rfl

/-- Every endomorphism of `(ℤ/m)|_Y` is the multiplication by the image of the section `1`. -/
lemma eq_zmodAbSheafOverMul {m : ℕ} {Y : X.ProEt}
    (f : zmodAbSheafOver m Y ⟶ zmodAbSheafOver m Y) :
    f = zmodAbSheafOverMul (f.hom.app (op (Over.mk (𝟙 Y))) (zmodAbSheafOver.mk _ 1)).down := by
  refine zmodAbSheafOver_hom_ext ?_
  exact (congrArg (zmodAbSheafOver.mk _) (mul_one _)).symm

/-- Multiplications by locally constant functions compose. -/
lemma zmodAbSheafOverMul_comp {m : ℕ} {Y : X.ProEt} (c d : C(Y.left, ZMod m)) :
    zmodAbSheafOverMul c ≫ zmodAbSheafOverMul d = zmodAbSheafOverMul (d * c) := by
  refine zmodAbSheafOver_hom_ext ?_
  exact congrArg (zmodAbSheafOver.mk _) (mul_assoc d c 1).symm

/-- Multiplication by `1` is the identity. -/
lemma zmodAbSheafOverMul_one {m : ℕ} {Y : X.ProEt} :
    zmodAbSheafOverMul (1 : C(Y.left, ZMod m)) = 𝟙 _ := by
  refine zmodAbSheafOver_hom_ext ?_
  exact congrArg (zmodAbSheafOver.mk _) (one_mul _)

/-- A locally constant function is determined by the multiplication by it. -/
lemma zmodAbSheafOverMul_injective {m : ℕ} {Y : X.ProEt} {c d : C(Y.left, ZMod m)}
    (h : zmodAbSheafOverMul c = zmodAbSheafOverMul d) : c = d := by
  have : c * 1 = d * 1 := congrArg (fun φ : zmodAbSheafOver m Y ⟶ zmodAbSheafOver m Y ↦
    (φ.hom.app (op (Over.mk (𝟙 Y))) (zmodAbSheafOver.mk _ 1)).down) h
  simpa only [mul_one] using this

end AlgebraicGeometry.ProEtale

namespace ZMod

open scoped Classical in
/-- A lift of an element of `ℤ/m` to a unit of `ℤ/m'`, for `m ∣ m'`: a unit lifting `z` if `z`
is a unit, and `1` otherwise. -/
noncomputable def unitsLift {m m' : ℕ} [NeZero m'] (h : m ∣ m') (z : ZMod m) : (ZMod m')ˣ :=
  if hz : IsUnit z then (unitsMap_surjective h hz.unit).choose else 1

/-- `ZMod.unitsLift` lifts units. -/
lemma castHom_unitsLift {m m' : ℕ} [NeZero m'] (h : m ∣ m') {z : ZMod m} (hz : IsUnit z) :
    castHom h (ZMod m) (unitsLift h z) = z := by
  rw [unitsLift, dite_eq_left hz]
  exact (congrArg Units.val (unitsMap_surjective h hz.unit).choose_spec).trans hz.unit_spec

end ZMod

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

/-- **Automorphisms of `(ℤ/ℓⁿ)|_Y` lift to `(ℤ/ℓⁿ⁺¹)|_Y`**: an automorphism `α` of `(ℤ/ℓⁿ)|_Y` is
the multiplication by a pointwise unit `u : Y → ℤ/ℓⁿ`, and the multiplication by a pointwise lift
of `u` to a unit of `ℤ/ℓⁿ⁺¹` is an automorphism of `(ℤ/ℓⁿ⁺¹)|_Y` lifting `α` along the
reduction. -/
theorem exists_iso_hom_comp_zmodPowAbSheafDiagram_map (n : ℕ) (Y : X.ProEt)
    (α : ((ProEt.topology X).overPullback Ab.{u + 1} Y).obj
        ((zmodPowAbSheafDiagram X l).obj (op n)) ≅
      ((ProEt.topology X).overPullback Ab.{u + 1} Y).obj
        ((zmodPowAbSheafDiagram X l).obj (op n))) :
    ∃ β : ((ProEt.topology X).overPullback Ab.{u + 1} Y).obj
        ((zmodPowAbSheafDiagram X l).obj (op (n + 1))) ≅
      ((ProEt.topology X).overPullback Ab.{u + 1} Y).obj
        ((zmodPowAbSheafDiagram X l).obj (op (n + 1))),
      β.hom ≫ ((ProEt.topology X).overPullback Ab.{u + 1} Y).map
          ((zmodPowAbSheafDiagram X l).map (homOfLE n.le_succ).op) =
        ((ProEt.topology X).overPullback Ab.{u + 1} Y).map
          ((zmodPowAbSheafDiagram X l).map (homOfLE n.le_succ).op) ≫ α.hom := by
  have : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hdvd : l ^ n ∣ l ^ (n + 1) := pow_dvd_pow l n.le_succ
  let u : C(Y.left, ZMod (l ^ n)) :=
    (α.hom.hom.app (op (Over.mk (𝟙 Y))) (zmodAbSheafOver.mk _ 1)).down
  let v : C(Y.left, ZMod (l ^ n)) :=
    (α.inv.hom.app (op (Over.mk (𝟙 Y))) (zmodAbSheafOver.mk _ 1)).down
  have hα : α.hom = zmodAbSheafOverMul u := eq_zmodAbSheafOverMul _
  have hα' : α.inv = zmodAbSheafOverMul v := eq_zmodAbSheafOverMul _
  have hvu : v * u = 1 := zmodAbSheafOverMul_injective (by
    rw [← zmodAbSheafOverMul_comp, ← hα, ← hα', α.hom_inv_id]
    exact zmodAbSheafOverMul_one.symm)
  have hu (t : Y.left) : IsUnit (u t) :=
    IsUnit.of_mul_eq_one_right (v t) (by simpa using congrArg (· t) hvu)
  let w : C(ZMod (l ^ n), ZMod (l ^ (n + 1))) :=
    ⟨fun z ↦ ZMod.unitsLift hdvd z, continuous_of_discreteTopology⟩
  let w' : C(ZMod (l ^ n), ZMod (l ^ (n + 1))) :=
    ⟨fun z ↦ ↑(ZMod.unitsLift hdvd z)⁻¹, continuous_of_discreteTopology⟩
  refine ⟨⟨zmodAbSheafOverMul (w.comp u), zmodAbSheafOverMul (w'.comp u), ?_, ?_⟩, ?_⟩
  · rw [zmodAbSheafOverMul_comp]
    refine Eq.trans ?_ zmodAbSheafOverMul_one
    congr 1
    ext t
    exact Units.inv_mul _
  · rw [zmodAbSheafOverMul_comp]
    refine Eq.trans ?_ zmodAbSheafOverMul_one
    congr 1
    ext t
    exact Units.mul_inv _
  · refine zmodAbSheafOver_hom_ext ?_
    rw [hα]
    refine ULift.ext (ContinuousMap.ext fun t ↦ ?_)
    exact (by simp only [map_one, mul_one, ZMod.castHom_unitsLift hdvd (hu t)] :
      ZMod.castHom hdvd (ZMod (l ^ n)) (ZMod.unitsLift hdvd (u t) * 1) =
        u t * ZMod.castHom hdvd (ZMod (l ^ n)) 1)

/-- **An `ℓ`-adic tower of sheaves locally isomorphic to `(ℤ/ℓⁿ)_X` has a lattice which is
locally `ℤ_ℓ,X`.** Let `(Gₙ)` be a tower of pro-étale abelian sheaves whose transitions are,
locally, cokernels of `ℓⁿ` (i.e. `Gₙ₊₁/ℓⁿ ≅ Gₙ`), with each `Gₙ` locally isomorphic to
`(ℤ/ℓⁿ)_X`. Then `lim Gₙ` is isomorphic to `ℤ_ℓ,X` over the members of a pro-étale cover of any
object. -/
theorem exists_cover_nonempty_iso_padicIntAbSheaf_of_locally_iso
    (G : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) Ab.{u + 1})
    (hG : ∀ (n : ℕ) (Y : X.ProEt), ∃ w : (((l ^ n : ℕ) : ℤ) • 𝟙 _) ≫
        ((ProEt.topology X).overPullback Ab.{u + 1} Y).map (G.map (homOfLE n.le_succ).op) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ w)))
    (hloc : ∀ (n : ℕ) (V : X.ProEt), ∃ S ∈ ProEt.topology X V,
      ∀ ⦃Y : X.ProEt⦄ (f : Y ⟶ V), S f →
        Nonempty ((isoPresheaf ((zmodPowAbSheafDiagram X l).obj (op n)) (G.obj (op n))).obj
          (op Y)))
    (V : X.ProEt) :
    ∃ (ι : Type u) (W : ι → X.ProEt) (f : ∀ i, W i ⟶ V),
      Sieve.ofArrows W f ∈ ProEt.topology X V ∧
      ∀ i, Nonempty (((ProEt.topology X).overPullback Ab.{u + 1} (W i)).obj (limit G) ≅
        ((ProEt.topology X).overPullback Ab.{u + 1} (W i)).obj (padicIntAbSheaf X l)) :=
  exists_cover_nonempty_iso_padicIntAbSheaf_of_lift_aut X l G hG hloc
    (fun n Y _ ↦ ⟨⊤, (ProEt.topology X).top_mem Y, fun Z _ _ ↦
      exists_iso_hom_comp_zmodPowAbSheafDiagram_map X l n Z _⟩) V

end AlgebraicGeometry.ProEtale
