/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import WeilConjectures.RingTheory.ProEtale.IndEtale
import WeilConjectures.RingTheory.EtaleAlgebraLift
import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale

/-!
# Lifting ind-étale algebras along a closed immersion

Let `A` be a ring and `C̄` an `A`-algebra. The category `N_A(C̄)` has as objects the
factorizations `A ⟶ B ⟶ C̄` with `B` étale (of finite presentation) over `A`, and as morphisms
the compatible `A`-algebra maps; its colimit

`H_A(C̄) = colim_{N_A(C̄)} B`

comes with an `A`-algebra map to `C̄` (blueprint
`proposition-extension-zero-restriction-closed-subscheme`). When `C̄` is an ind-étale algebra over
`A ⧸ I`, `H_A(C̄)` is an ind-étale `A`-algebra lifting `C̄`: the reduction
`H_A(C̄) ⧸ I H_A(C̄) ⟶ C̄` is an isomorphism (blueprint
`proposition-extension-zero-restriction-closed-subscheme`). This is the ring-theoretic input to
lifting pro-étale coverings of a closed subscheme
(`proposition-extension-zero-restriction-closed-subscheme`).

## Implementation notes

The objects of `N_A(C̄)` are taken to be the quotients `A[x₁, …, xₙ] ⧸ J` that are étale over
`A`, so that `N_A(C̄)` is a small category (`Algebra.ClosedLift.Index`); every étale algebra of
finite presentation is isomorphic to such a quotient, so this is a skeleton-like small model of
the blueprint's indexing category, with the same colimit.

The two facts about this construction that belong to the subsection
`proposition-extension-zero-restriction-closed-subscheme` of the blueprint, that `N_A(C̄)` is
filtered (`proposition-extension-zero-restriction-closed-subscheme`) and the reduction isomorphism
(`proposition-extension-zero-restriction-closed-subscheme`), are stated here for use downstream.

## Main definitions

- `Algebra.ClosedLift.Index`: the indexing category `N_A(C̄)`.
- `Algebra.ClosedLift`: the `A`-algebra `H_A(C̄)`.
- `Algebra.ClosedLift.toAlgHom`: its map `H_A(C̄) ⟶ C̄`.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped TensorProduct

namespace Algebra

variable (A : Type u) [CommRing A] (C : Type u) [CommRing C] [Algebra A C]

namespace ClosedLift

/-- The objects of the indexing category `N_A(C̄)` of blueprint
`proposition-extension-zero-restriction-closed-subscheme`: an étale `A`-algebra, presented as a
quotient `A[x₁, …, xₙ] ⧸ J`, together with an `A`-algebra map to `C̄`. -/
structure Index where
  /-- The number of variables of the presentation. -/
  n : ℕ
  /-- The ideal of relations of the presentation. -/
  rel : Ideal (MvPolynomial (Fin n) A)
  etale : Algebra.Etale A (MvPolynomial (Fin n) A ⧸ rel)
  /-- The map to `C̄`. -/
  toC : (MvPolynomial (Fin n) A ⧸ rel) →ₐ[A] C

variable {A C}

/-- The étale `A`-algebra underlying an object of `N_A(C̄)`. -/
abbrev Index.alg (X : Index A C) : Type u := MvPolynomial (Fin X.n) A ⧸ X.rel

instance (X : Index A C) : Algebra.Etale A X.alg := X.etale

/-- The morphisms of `N_A(C̄)`: the `A`-algebra maps compatible with the maps to `C̄`. -/
@[ext]
structure Index.Hom (X Y : Index A C) where
  /-- The underlying `A`-algebra map. -/
  hom : X.alg →ₐ[A] Y.alg
  comp_toC : Y.toC.comp hom = X.toC

noncomputable instance : SmallCategory (Index A C) where
  Hom := Index.Hom
  id X := ⟨AlgHom.id A _, rfl⟩
  comp f g := ⟨g.hom.comp f.hom, by rw [← AlgHom.comp_assoc, g.comp_toC, f.comp_toC]⟩

@[simp]
lemma Index.id_hom (X : Index A C) : Index.Hom.hom (𝟙 X) = AlgHom.id A _ := rfl

@[simp]
lemma Index.comp_hom {X Y Z : Index A C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Index.Hom.hom (f ≫ g) = g.hom.comp f.hom := rfl

variable (A C)

/-- The diagram `N_A(C̄) ⥤ CommAlgCat A` sending a factorization `A ⟶ B ⟶ C̄` to `B`. -/
noncomputable def diagram : Index A C ⥤ CommAlgCat.{u} A where
  obj X := CommAlgCat.of A X.alg
  map f := CommAlgCat.ofHom f.hom

/-- The cocone over `ClosedLift.diagram A C` with point `C̄`, given by the maps to `C̄`. -/
noncomputable def coconeC : Cocone (diagram A C) where
  pt := CommAlgCat.of A C
  ι :=
    { app X := CommAlgCat.ofHom X.toC
      naturality X Y f := by
        ext x
        simp only [diagram, Functor.const_obj_map]
        exact DFunLike.congr_fun f.comp_toC x }

end ClosedLift

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`: for an `A`-algebra `C̄`,
the `A`-algebra `H_A(C̄) = colim_{N_A(C̄)} B`, the colimit of the étale `A`-algebras `B` with an
`A`-algebra map to `C̄`. -/
def ClosedLift : Type u :=
  (colimit (ClosedLift.diagram A C) : CommAlgCat.{u} A)

noncomputable instance : CommRing (ClosedLift A C) :=
  inferInstanceAs (CommRing (colimit (ClosedLift.diagram A C) : CommAlgCat.{u} A))

noncomputable instance : Algebra A (ClosedLift A C) :=
  inferInstanceAs (Algebra A (colimit (ClosedLift.diagram A C) : CommAlgCat.{u} A))

namespace ClosedLift

/-- The map `H_A(C̄) ⟶ C̄` of blueprint `proposition-extension-zero-restriction-closed-subscheme`,
induced by the maps `B ⟶ C̄` of the objects of `N_A(C̄)`. -/
noncomputable def toAlgHom : ClosedLift A C →ₐ[A] C :=
  (colimit.desc (diagram A C) (coconeC A C)).hom

/-- The colimit presentation of `H_A(C̄)` by the étale algebras of `N_A(C̄)`. -/
noncomputable def colimitPresentation :
    ColimitPresentation (Index A C) (CommAlgCat.of A (ClosedLift A C)) where
  diag := diagram A C
  ι := (colimit.cocone (diagram A C)).ι
  isColimit := colimit.isColimit (diagram A C)

private theorem exists_index (B : Type u) [CommRing B] [Algebra A B]
    [Algebra.Etale A B] (q : B →ₐ[A] C) :
    ∃ (X : Index A C) (e : X.alg ≃ₐ[A] B), X.toC = q.comp e.toAlgHom := by
  obtain ⟨n, J, e, _⟩ := Algebra.FinitePresentation.iff.mp
    (inferInstance : Algebra.FinitePresentation A B)
  exact ⟨⟨n, J, Algebra.Etale.of_equiv e.symm, q.comp e.toAlgHom⟩, e, rfl⟩

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme` (subsection
`proposition-extension-zero-restriction-closed-subscheme`): the indexing category `N_A(C̄)` of
`proposition-extension-zero-restriction-closed-subscheme` is filtered. -/
instance isFiltered_index : IsFiltered (Index A C) := by
  exact {
    nonempty := by
      obtain ⟨X, _, _⟩ := exists_index A C A (Algebra.ofId A C)
      exact ⟨X⟩
    cocone_objs X Y := by
      let q : X.alg ⊗[A] Y.alg →ₐ[A] C :=
        Algebra.TensorProduct.productMap X.toC Y.toC
      have : Algebra.Etale A (X.alg ⊗[A] Y.alg) :=
        Algebra.Etale.comp A X.alg _
      obtain ⟨Z, e, he⟩ := exists_index A C _ q
      refine ⟨Z, ⟨e.symm.toAlgHom.comp Algebra.TensorProduct.includeLeft, ?_⟩,
        ⟨e.symm.toAlgHom.comp Algebra.TensorProduct.includeRight, ?_⟩, trivial⟩
      · ext x
        simp [he, q]
      · ext y
        simp [he, q]
    cocone_maps {X Y} f g := by
      let h : X.alg ⊗[A] X.alg →ₐ[A] Y.alg :=
        Algebra.TensorProduct.productMap f.hom g.hom
      let K := KaehlerDifferential.ideal A X.alg
      let J : Ideal Y.alg := K.map h.toRingHom
      have hK : IsIdempotentElem K :=
        (Ideal.cotangent_subsingleton_iff K).mp
          (inferInstanceAs (Subsingleton Ω[X.alg⁄A]))
      have hJ : IsIdempotentElem J := by
        change J * J = J
        rw [← Ideal.map_mul, hK]
      have hJfg : J.FG := (KaehlerDifferential.ideal_fg A X.alg).map _
      have : Algebra.FinitePresentation Y.alg (Y.alg ⧸ J) :=
        Algebra.FinitePresentation.quotient hJfg
      have : Algebra.FormallyEtale Y.alg (Y.alg ⧸ J) := by
        apply (Algebra.FormallyEtale.iff_of_surjective
          (Ideal.Quotient.mk_surjective (I := J))).mpr
        simpa only [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker] using hJ
      have : Algebra.Etale Y.alg (Y.alg ⧸ J) := ⟨inferInstance, inferInstance⟩
      have : Algebra.Etale A (Y.alg ⧸ J) := Algebra.Etale.comp A Y.alg _
      have hcomp : Y.toC.comp h = X.toC.comp (Algebra.TensorProduct.lmul' A) := by
        apply Algebra.TensorProduct.ext
        · ext x
          simpa [h] using DFunLike.congr_fun f.comp_toC x
        · ext x
          simpa [h] using DFunLike.congr_fun g.comp_toC x
      have hker : J ≤ RingHom.ker Y.toC.toRingHom := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        change Y.toC (h x) = 0
        rw [← AlgHom.comp_apply, hcomp, AlgHom.comp_apply]
        change Algebra.TensorProduct.lmul' A x = 0 at hx
        rw [hx, map_zero]
      let q : (Y.alg ⧸ J) →ₐ[A] C := Ideal.Quotient.liftₐ J Y.toC hker
      obtain ⟨Z, e, he⟩ := exists_index A C _ q
      let a : Y ⟶ Z := ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ A J), by
        ext y
        simp [he, q]⟩
      refine ⟨Z, a, ?_⟩
      apply Index.Hom.ext
      apply AlgHom.ext
      intro x
      change e.symm (Ideal.Quotient.mk J (f.hom x)) =
        e.symm (Ideal.Quotient.mk J (g.hom x))
      congr 1
      apply Ideal.Quotient.eq.mpr
      have hx : x ⊗ₜ[A] (1 : X.alg) - (1 : X.alg) ⊗ₜ[A] x ∈ K := by
        change Algebra.TensorProduct.lmul' A _ = 0
        simp
      have hm := Ideal.mem_map_of_mem h.toRingHom hx
      simpa [h, J] using hm
 }

/-- `H_A(C̄)` is ind-étale over `A`: it is the filtered colimit of the étale algebras of
`N_A(C̄)`. -/
instance indEtale : Algebra.IndEtale A (ClosedLift A C) :=
  ⟨⟨Index A C, inferInstance, inferInstance, colimitPresentation A C,
    fun X ↦ inferInstanceAs (Algebra.Etale A X.alg)⟩⟩

/-- The map to the input algebra agrees with the index map on each colimit structure map. -/
theorem toAlgHom_ι (X : Index A C) (x : X.alg) :
    toAlgHom A C ((colimit.ι (diagram A C) X).hom x) = X.toC x := by
  change ((colimit.ι (diagram A C) X ≫ colimit.desc _ (coconeC A C)).hom) x = _
  rw [colimit.ι_desc]
  rfl

private theorem exists_rep (x : ClosedLift A C) :
    ∃ (X : Index A C) (b : X.alg), (colimit.ι (diagram A C) X).hom b = x := by
  exact Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget (CommAlgCat A)) (colimit.isColimit (diagram A C))) x

/-- An element of `H_A(C̄)` whose image in `C̄` is a unit is a unit: lift the inverse along a
localization of a representing étale stage. -/
theorem isUnit_of_isUnit_image (x : ClosedLift A C)
    (hx : IsUnit (toAlgHom A C x)) : IsUnit x := by
  obtain ⟨X, b, rfl⟩ := exists_rep A C x
  rw [toAlgHom_ι] at hx
  let q : Localization.Away b →ₐ[A] C := IsLocalization.Away.liftAlgHom b hx
  obtain ⟨Y, e, he⟩ := exists_index A C _ q
  let f : X ⟶ Y := ⟨e.symm.toAlgHom.comp (IsScalarTower.toAlgHom A X.alg _), by
    ext a
    simp [he, q]⟩
  have hrep : (colimit.ι (diagram A C) X).hom b =
      (colimit.ι (diagram A C) Y).hom (e.symm (algebraMap X.alg _ b)) := by
    have hw := colimit.w (diagram A C) f
    exact (DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom hw) b).symm
  rw [hrep]
  exact ((IsLocalization.Away.algebraMap_isUnit b).map e.symm.toMonoidHom).map
    (colimit.ι (diagram A C) Y).hom.toMonoidHom

variable (I : Ideal A) [Algebra (A ⧸ I) C] [IsScalarTower A (A ⧸ I) C]

/-- The map `H_A(C̄) ⟶ C̄` kills `I H_A(C̄)` when `C̄` is an `A ⧸ I`-algebra. -/
lemma map_le_ker_toAlgHom :
    I.map (algebraMap A (ClosedLift A C)) ≤ RingHom.ker (toAlgHom A C : ClosedLift A C →+* C) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  simp only [Ideal.mem_comap, RingHom.mem_ker, RingHom.coe_coe, AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply A (A ⧸ I) C, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]

/-- The reduction `H_A(C̄) ⧸ I H_A(C̄) ⟶ C̄` of blueprint
`proposition-extension-zero-restriction-closed-subscheme`. -/
noncomputable def reduction :
    ClosedLift A C ⧸ I.map (algebraMap A (ClosedLift A C)) →+* C :=
  Ideal.Quotient.lift _ (toAlgHom A C : ClosedLift A C →+* C) (map_le_ker_toAlgHom A C I)

/-- The map `H_A(C̄) ⟶ C̄` is surjective when `C̄` is ind-étale over `A ⧸ I`. -/
theorem surjective_toAlgHom [Algebra.IndEtale (A ⧸ I) C] :
    Function.Surjective (toAlgHom A C) := by
  intro c
  obtain ⟨ι, _, _, P, hP⟩ :=
    Algebra.IndEtale.exists_colimitPresentation (R := A ⧸ I) (S := C)
  obtain ⟨i, b, hb⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget (CommAlgCat (A ⧸ I))) P.isColimit) c
  let : Algebra A (P.diag.obj i) :=
    (algebraMap (A ⧸ I) (P.diag.obj i)).comp (algebraMap A (A ⧸ I)) |>.toAlgebra
  have : IsScalarTower A (A ⧸ I) (P.diag.obj i) :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have : Algebra.Etale (A ⧸ I) (P.diag.obj i) := hP i
  obtain ⟨m, Q, L, hL, _, e, he⟩ := Algebra.exists_etale_coefficientLift I (P.diag.obj i)
  have : Algebra.Etale A L.LiftRing := hL
  let q₀ : L.LiftRing →ₐ[A] P.diag.obj i :=
    { __ := L.reduction
      commutes' a := by
        change L.polynomialReduction (MvPolynomial.C a) = _
        simp [Algebra.SquareJacobianPresentation.CoefficientLift.polynomialReduction]
        rfl }
  let φ : P.diag.obj i →ₐ[A ⧸ I] C := (P.ι.app i).hom
  let q : L.LiftRing →ₐ[A] C := (φ.restrictScalars A).comp q₀
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e.symm b)
  have hqa : q a = c := by
    change (P.ι.app i).hom (L.reduction a) = c
    rw [← he, ha, e.apply_symm_apply]
    exact hb
  obtain ⟨X, f, hf⟩ := exists_index A C _ q
  refine ⟨(colimit.ι (diagram A C) X).hom (f.symm a), ?_⟩
  rw [toAlgHom_ι, hf]
  simpa using hqa

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme` (subsection
`proposition-extension-zero-restriction-closed-subscheme`): for an ind-étale `A ⧸ I`-algebra `C̄`,
the reduction `H_A(C̄) ⧸ I H_A(C̄) ⟶ C̄` of the lift `H_A(C̄)` of
`proposition-extension-zero-restriction-closed-subscheme` is an isomorphism. -/
theorem bijective_reduction [Algebra.IndEtale (A ⧸ I) C] :
    Function.Bijective (reduction A C I) := by
  let H := ClosedLift A C
  let J := I.map (algebraMap A H)
  let R := H ⧸ J
  let r : R →ₐ[A ⧸ I] C :=
    { __ := reduction A C I
      commutes' a := by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        change toAlgHom A C (algebraMap A H a) = _
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A (A ⧸ I) C]
        rfl }
  have hr : Function.Surjective r := by
    intro c
    obtain ⟨x, hx⟩ := surjective_toAlgHom A C I c
    exact ⟨Ideal.Quotient.mk J x, hx⟩
  have hbase : Algebra.IndEtale (A ⧸ I) ((A ⧸ I) ⊗[A] H) :=
    (RingHom.IndEtale.algebraMap_iff _ _).mp
      (RingHom.IndEtale.isStableUnderBaseChange.tensorProduct (A ⧸ I)
        ((RingHom.IndEtale.algebraMap_iff A H).mpr inferInstance))
  have hR : Algebra.IndEtale (A ⧸ I) R := by
    rw [Algebra.IndEtale.iff_ind_etale] at hbase ⊢
    exact (CommAlgCat.etale (A ⧸ I)).ind.prop_of_iso
      (CommAlgCat.isoMk (Algebra.TensorProduct.quotIdealMapEquivQuotTensor H I).symm) hbase
  have hrel : r.toRingHom.IndEtale := by
    apply RingHom.IndEtale.of_comp
      ((RingHom.IndEtale.algebraMap_iff (A ⧸ I) R).mpr hR)
    rw [show r.toRingHom.comp (algebraMap (A ⧸ I) R) = algebraMap (A ⧸ I) C from
      RingHom.ext r.commutes]
    exact (RingHom.IndEtale.algebraMap_iff _ _).mpr inferInstance
  let : Algebra R C := r.toRingHom.toAlgebra
  have : Algebra.IndEtale R C := hrel
  have : Module.Flat R C := inferInstance
  let r' : R →ₐ[R] C := Algebra.ofId R C
  have hr' : Function.Surjective r' := hr
  have : (RingHom.ker r.toRingHom).Pure :=
    Module.Flat.of_linearEquiv (Ideal.quotientKerAlgEquivOfSurjective hr').toLinearEquiv
  refine ⟨?_, hr⟩
  apply (injective_iff_map_eq_zero (r.toRingHom)).mpr
  intro x hx
  obtain ⟨e, he, hxe⟩ :=
    Ideal.exists_eq_mul_of_pure (show x ∈ RingHom.ker r.toRingHom from hx)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective e
  have hy : toAlgHom A C y = 0 := he
  have hu : IsUnit (1 - y) := isUnit_of_isUnit_image A C _ (by simp [hy])
  have hunit : IsUnit (1 - Ideal.Quotient.mk J y) := by
    simpa only [map_sub, map_one] using hu.map (Ideal.Quotient.mk J)
  apply hunit.mul_left_eq_zero.mp
  rw [mul_sub, mul_one, ← hxe, sub_self]

end ClosedLift

end Algebra
