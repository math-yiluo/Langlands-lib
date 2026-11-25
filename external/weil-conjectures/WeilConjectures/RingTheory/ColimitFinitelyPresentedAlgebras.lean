/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.ConeCategory
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.RingTheory.FiniteStability
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# An algebra as the filtered colimit of finitely presented algebras over it

Source: Stacks Project, Tag 0BUF, Lemma `lemma-ring-colimit-fp-category` and its footnote
(blueprint: theorem-finite-etale-covers-proper-henselian--2).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CommAlgCat

/-- Stacks Project, Tag 0BUF, Lemma `lemma-ring-colimit-fp-category`, with a set `P`
containing a representative of each finitely presented algebra.
(blueprint: theorem-finite-etale-covers-proper-henselian--2).

`P` being a set of algebras of `CommAlgCat.{max u v} R` is `ObjectProperty.Small.{max u v} P`;
`I` being small is `Small.{max u v}` of its objects (its hom types lie in `Type (max u v)`).

The full subcategory `P.FullSubcategory` has all algebra maps between its objects, so
`CostructuredArrow P.ι Λ` has precisely the pairs `(A, α : A ⟶ Λ)` and commuting triangles
in the statement. The cocone below has vertex `Λ` and component `α` at `(A, α)`.

Proof from the node, following Tag 0BUF:
1. The objects `(A, α)` have `A` in the set `P` and `α` in the set of algebra maps
   `A ⟶ Λ`, so they form a set and the index is small. A representative of `R`, with its
   structure map to `Λ`, makes the index nonempty
   (def-weil-pbc-finitely-presented-algebra).
2. Representatives of tensor products give common upper bounds
   (lem-weil-pbc-tensor-product-finitely-presented-algebras).
3. Quotient the target of parallel arrows by the differences of their values on finitely
   many algebra generators, then choose its representative. This equalizes the arrows
   (lem-weil-pbc-finite-presentation-quotient-fg-ideal). Thus the index is filtered.
4. Take the colimit `B` in commutative algebras and its canonical map `B ⟶ Λ`
   (lem-weil-pbc-commutative-algebras-colimits-exist, def-weil-pbc-category-colimit).
5. Each element of `Λ` is hit using evaluation from `R[x]`, so this map is surjective.
6. Represent an element of its kernel in a stage, then quotient that stage by the
   principal ideal it generates. This kills the element in the colimit
   (lem-weil-pbc-filtered-colimit-algebras-elementwise,
   lem-weil-pbc-finite-presentation-quotient-fg-ideal), proving injectivity.
7. Transport the colimit property along the resulting algebra isomorphism `B ≅ Λ`
   (def-weil-pbc-category-colimit). -/
theorem isFiltered_and_isColimit_finitelyPresentedAlgebras
    (R : Type u) [CommRing R] (Λ : CommAlgCat.{max u v} R)
    (P : ObjectProperty (CommAlgCat.{max u v} R)) [ObjectProperty.Small.{max u v} P]
    (hfp : ∀ A : CommAlgCat.{max u v} R, P A → Algebra.FinitePresentation R A)
    (hrep : ∀ A : CommAlgCat.{max u v} R, Algebra.FinitePresentation R A →
      ∃ B : P.FullSubcategory, Nonempty (A ≅ B.obj)) :
    Small.{max u v} (CostructuredArrow P.ι Λ) ∧ IsFiltered (CostructuredArrow P.ι Λ) ∧
      Nonempty (IsColimit (Cocone.fromCostructuredArrow P.ι
        (𝟭 (CostructuredArrow P.ι Λ)))) := by
  classical
  have hsmall : Small.{max u v} (CostructuredArrow P.ι Λ) := inferInstance
  let A₀ : CommAlgCat.{max u v} R := .of R (ULift.{v} R)
  have hA₀ : Algebra.FinitePresentation R A₀ :=
    Algebra.FinitePresentation.equiv (ULift.algEquiv.symm : R ≃ₐ[R] ULift.{v} R)
  obtain ⟨B, ⟨e⟩⟩ := hrep A₀ hA₀
  let α : A₀ ⟶ Λ := ofHom
    ((Algebra.ofId R Λ).comp ULift.algEquiv.toAlgHom)
  have hnonempty : Nonempty (CostructuredArrow P.ι Λ) :=
    ⟨CostructuredArrow.mk (Y := B) (e.inv ≫ α)⟩
  -- Tensor products provide common successors.
  have hcommon : ∀ x y : CostructuredArrow P.ι Λ,
      ∃ (z : CostructuredArrow P.ι Λ) (_ : x ⟶ z) (_ : y ⟶ z), True := by
    intro x y
    let A := x.left.obj
    let B := y.left.obj
    let : Algebra.FinitePresentation R A := hfp _ x.left.property
    let : Algebra.FinitePresentation R B := hfp _ y.left.property
    let T : CommAlgCat.{max u v} R := .of R (TensorProduct R A B)
    have hT : Algebra.FinitePresentation R T :=
      Algebra.FinitePresentation.trans R A (TensorProduct R A B)
    obtain ⟨C, ⟨e⟩⟩ := hrep T hT
    let β : T ⟶ Λ := ofHom (Algebra.TensorProduct.lift x.hom.hom y.hom.hom
      (fun a b ↦ Commute.all _ _))
    let i : A ⟶ T := ofHom Algebra.TensorProduct.includeLeft
    let j : B ⟶ T := ofHom Algebra.TensorProduct.includeRight
    let z : CostructuredArrow P.ι Λ := CostructuredArrow.mk (Y := C) (e.inv ≫ β)
    refine ⟨z, CostructuredArrow.homMk (ObjectProperty.homMk (i ≫ e.hom)) ?_,
      CostructuredArrow.homMk (ObjectProperty.homMk (j ≫ e.hom)) ?_, trivial⟩
    · change (i ≫ e.hom) ≫ (e.inv ≫ β) = x.hom
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      apply CommAlgCat.hom_ext
      exact Algebra.TensorProduct.lift_comp_includeLeft _ _ (fun _ _ ↦ Commute.all _ _)
    · change (j ≫ e.hom) ≫ (e.inv ≫ β) = y.hom
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      apply CommAlgCat.hom_ext
      exact Algebra.TensorProduct.lift_comp_includeRight' _ _ (fun _ _ ↦ Commute.all _ _)
  -- Kill the differences on a finite polynomial generating family.
  have hequalizing
      (A B Λ : CommAlgCat.{max u v} R)
      (hA : Algebra.FinitePresentation R A) (hB : Algebra.FinitePresentation R B)
      (f g : A ⟶ B) (α : B ⟶ Λ) (h : f ≫ α = g ≫ α) :
      ∃ (C : CommAlgCat.{max u v} R), Algebra.FinitePresentation R C ∧
        ∃ (q : B ⟶ C) (β : C ⟶ Λ), q ≫ β = α ∧ f ≫ q = g ≫ q := by
    let : Algebra.FinitePresentation R A := hA
    let : Algebra.FinitePresentation R B := hB
    obtain ⟨n, π, hπ, _⟩ := Algebra.FinitePresentation.out (R := R) (A := A)
    let d : Fin n → B := fun i ↦ f (π (MvPolynomial.X i)) - g (π (MvPolynomial.X i))
    let J : Ideal B := Ideal.span (Set.range d)
    have hJ : J.FG := by
      exact ⟨Finset.univ.image d, by simp [J]⟩
    have hker : J ≤ RingHom.ker α.hom.toRingHom := by
      apply Ideal.span_le.mpr
      rintro b ⟨i, rfl⟩
      change α (d i) = 0
      have hi : α (f (π (MvPolynomial.X i))) = α (g (π (MvPolynomial.X i))) :=
        ConcreteCategory.congr_hom h _
      simpa [d, map_sub, sub_eq_zero] using hi
    let C : CommAlgCat.{max u v} R := .of R (B ⧸ J)
    let q : B ⟶ C := ofHom (Ideal.Quotient.mkₐ R J)
    let β : C ⟶ Λ := ofHom (Ideal.Quotient.liftₐ J α.hom (fun b hb ↦ hker hb))
    refine ⟨C, Algebra.FinitePresentation.quotient hJ, q, β, ?_, ?_⟩
    · apply CommAlgCat.hom_ext
      exact Ideal.Quotient.liftₐ_comp _ _ _
    · apply CommAlgCat.hom_ext
      have hpoly : (q.hom.comp f.hom).comp π = (q.hom.comp g.hom).comp π := by
        apply MvPolynomial.algHom_ext
        intro i
        change Ideal.Quotient.mk J (f (π (MvPolynomial.X i))) =
          Ideal.Quotient.mk J (g (π (MvPolynomial.X i)))
        apply Ideal.Quotient.eq.mpr
        exact Ideal.subset_span ⟨i, rfl⟩
      apply AlgHom.ext
      intro a
      obtain ⟨p, rfl⟩ := hπ a
      exact DFunLike.congr_fun hpoly p
  have hequalize : ∀ (x y : CostructuredArrow P.ι Λ) (f g : x ⟶ y),
      ∃ (z : CostructuredArrow P.ι Λ) (q : y ⟶ z), f ≫ q = g ≫ q := by
    intro x y f g
    have h : f.left.hom ≫ y.hom = g.left.hom ≫ y.hom := by
      exact f.w.trans g.w.symm
    obtain ⟨C, hC, q, β, hq, hfg⟩ :=
      hequalizing _ _ Λ (hfp _ x.left.property) (hfp _ y.left.property)
        f.left.hom g.left.hom y.hom h
    obtain ⟨B, ⟨e⟩⟩ := hrep C hC
    let z : CostructuredArrow P.ι Λ := CostructuredArrow.mk (Y := B) (e.inv ≫ β)
    have hw : (q ≫ e.hom) ≫ (e.inv ≫ β) = y.hom := by
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hq
    refine ⟨z, CostructuredArrow.homMk (ObjectProperty.homMk (q ≫ e.hom)) hw, ?_⟩
    apply CostructuredArrow.hom_ext
    apply ObjectProperty.hom_ext
    change f.left.hom ≫ (q ≫ e.hom) = g.left.hom ≫ (q ≫ e.hom)
    rw [← Category.assoc, ← Category.assoc, hfg]
  let : IsFiltered (CostructuredArrow P.ι Λ) :=
    { cocone_objs := hcommon
      cocone_maps := fun {x y} f g ↦ hequalize x y f g
      nonempty := hnonempty }
  -- Recognize the colimit in sets, then verify that its desc maps are algebra maps.
  have hcolimit : Nonempty (IsColimit (Cocone.fromCostructuredArrow P.ι
      (𝟭 (CostructuredArrow P.ι Λ)))) := by
    let I := CostructuredArrow P.ι Λ
    let c := Cocone.fromCostructuredArrow P.ι (𝟭 I)
    let t := (forget (CommAlgCat.{max u v} R)).mapCocone c
    have hsurj : ∀ x : Λ, ∃ (j : I) (a : j.left.obj), x = j.hom a := by
      intro x
      let A : CommAlgCat.{max u v} R :=
        .of R (MvPolynomial (ULift.{v} (Fin 1)) R)
      have hA : Algebra.FinitePresentation R A := inferInstance
      obtain ⟨B, ⟨e⟩⟩ := hrep A hA
      let α : A ⟶ Λ := ofHom (MvPolynomial.aeval (R := R) (fun _ ↦ x))
      let j : I := CostructuredArrow.mk (Y := B) (e.inv ≫ α)
      refine ⟨j, e.hom (MvPolynomial.X ⟨0⟩), ?_⟩
      change x = α (e.inv (e.hom (MvPolynomial.X ⟨0⟩)))
      rw [CommAlgCat.inv_hom_apply]
      exact (MvPolynomial.aeval_X (R := R) (fun _ ↦ x)
        (ULift.up (0 : Fin 1))).symm
    have hinj : ∀ (i : I) (a b : i.left.obj), i.hom a = i.hom b →
        ∃ (j : I) (q : i ⟶ j), q.left.hom a = q.left.hom b := by
      intro i a b hab
      let A := i.left.obj
      let J : Ideal A := Ideal.span {a - b}
      let : Algebra.FinitePresentation R A := hfp _ i.left.property
      have hJ : J.FG := ⟨{a - b}, by simp [J]⟩
      have hker : J ≤ RingHom.ker i.hom.hom.toRingHom := by
        apply Ideal.span_le.mpr
        rintro x (rfl : x = a - b)
        change i.hom (a - b) = 0
        rw [map_sub]
        exact sub_eq_zero.mpr hab
      let C : CommAlgCat.{max u v} R := .of R (A ⧸ J)
      have hC : Algebra.FinitePresentation R C := Algebra.FinitePresentation.quotient hJ
      let q : A ⟶ C := ofHom (Ideal.Quotient.mkₐ R J)
      let β : C ⟶ Λ := ofHom (Ideal.Quotient.liftₐ J i.hom.hom (fun x hx ↦ hker hx))
      have hq : q ≫ β = i.hom := by
        apply CommAlgCat.hom_ext
        exact Ideal.Quotient.liftₐ_comp _ _ _
      obtain ⟨B, ⟨e⟩⟩ := hrep C hC
      let j : I := CostructuredArrow.mk (Y := B) (e.inv ≫ β)
      have hw : (q ≫ e.hom) ≫ (e.inv ≫ β) = i.hom := by
        simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hq
      refine ⟨j, CostructuredArrow.homMk (ObjectProperty.homMk (q ≫ e.hom)) hw, ?_⟩
      change e.hom (q a) = e.hom (q b)
      apply congrArg e.hom
      apply Ideal.Quotient.eq.mpr
      exact Ideal.subset_span (Set.mem_singleton _)
    have ht : IsColimit t := Types.FilteredColimit.isColimitOf' _ t hsurj hinj
    have hpairs : ∀ x y : Λ, ∃ (j : I) (a b : j.left.obj),
        j.hom a = x ∧ j.hom b = y := by
      intro x y
      obtain ⟨i, a, hx⟩ := hsurj x
      obtain ⟨j, b, hy⟩ := hsurj y
      let k := IsFiltered.max i j
      let f : i ⟶ k := IsFiltered.leftToMax i j
      let g : j ⟶ k := IsFiltered.rightToMax i j
      refine ⟨k, f.left.hom a, g.left.hom b, ?_, ?_⟩
      · exact (ConcreteCategory.congr_hom f.w a).trans hx.symm
      · exact (ConcreteCategory.congr_hom g.w b).trans hy.symm
    let j₀ : I := Classical.choice IsFiltered.nonempty
    have hdesc : ∀ s : Cocone (𝟭 I ⋙ CostructuredArrow.proj P.ι Λ ⋙ P.ι),
        ∃ (d : Λ ⟶ s.pt), ∀ (j : I), j.hom ≫ d = s.ι.app j := by
      intro s
      let st := (forget (CommAlgCat.{max u v} R)).mapCocone s
      let d : Λ → s.pt := ht.desc st
      have hd : ∀ (j : I) (a : j.left.obj), d (j.hom a) = s.ι.app j a := by
        intro j a
        exact ConcreteCategory.congr_hom (ht.fac st j) a
      have hzero : d 0 = 0 := by
        have h := hd j₀ 0
        simpa only [map_zero] using h
      have hone : d 1 = 1 := by
        have h := hd j₀ 1
        simpa only [map_one] using h
      have hadd : ∀ x y : Λ, d (x + y) = d x + d y := by
        intro x y
        obtain ⟨j, a, b, rfl, rfl⟩ := hpairs x y
        rw [← map_add j.hom.hom, hd, map_add, hd, hd]
      have hmul : ∀ x y : Λ, d (x * y) = d x * d y := by
        intro x y
        obtain ⟨j, a, b, rfl, rfl⟩ := hpairs x y
        rw [← map_mul j.hom.hom, hd, map_mul, hd, hd]
      have hcomm : ∀ r : R, d (algebraMap R Λ r) = algebraMap R s.pt r := by
        intro r
        rw [← j₀.hom.hom.commutes r, hd]
        exact (s.ι.app j₀).hom.commutes r
      let δ : Λ ⟶ s.pt := ofHom
        { toFun := d
          map_zero' := hzero
          map_one' := hone
          map_add' := hadd
          map_mul' := hmul
          commutes' := hcomm }
      refine ⟨δ, ?_⟩
      intro j
      apply CommAlgCat.hom_ext
      exact AlgHom.ext (hd j)
    refine ⟨{ desc := fun s ↦ (hdesc s).choose
              fac := fun s j ↦ (hdesc s).choose_spec j
              uniq := ?_ }⟩
    intro s m hm
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    obtain ⟨j, a, rfl⟩ := hsurj x
    have h₁ := ConcreteCategory.congr_hom (hm j) a
    have h₂ := ConcreteCategory.congr_hom ((hdesc s).choose_spec j) a
    exact h₁.trans h₂.symm
  exact ⟨hsmall, inferInstance, hcolimit⟩

end CommAlgCat
