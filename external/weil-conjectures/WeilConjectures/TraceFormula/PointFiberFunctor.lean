/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Abelian.Projective.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Projective
public import WeilConjectures.CategoryTheory.DerivedCategory.FieldDevissage
public import WeilConjectures.CategoryTheory.DerivedCategory.ShiftSumFullyFaithful
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedProjective
public import WeilConjectures.TraceFormula.Basic
public import WeilConjectures.TraceFormula.CategoricalTraceExact
public import WeilConjectures.WeilObject.Sheaf.StalkFiniteFree

/-!
# The point category, evaluated

Let `k` be a separably closed field and `s = Spec k`. The unit `ℚ̲̄_ℓ,s` of the abelian category
`Mod_{ℚ̲̄_ℓ,s}` of `ℚ̲̄_ℓ`-modules on `s_proét` is projective
(`AlgebraicGeometry.ProEtale.projective_regular_of_isSepClosed`), with endomorphism ring `ℚ̄_ℓ`.
Hence its global sections `Γ = Hom(ℚ̲̄_ℓ,s, -) : Mod_{ℚ̲̄_ℓ,s} ⥤ Mod_{ℚ̄_ℓ}`
(`ProEtale.CondensedRing.pointSections`) are exact, and induce a triangulated functor
`Fib_s : Dᵇc(s)⟦ℚ̲̄_ℓ⟧ ⥤ D(ℚ̄_ℓ)` (`ProEtale.CondensedRing.pointFiberFunctor`).

Every object of `Dᵇc(s)⟦ℚ̲̄_ℓ⟧` is bounded with finite free cohomology sheaves
(`ProEtale.CondensedRing.isFiniteFree_upperStar_homology`), so it is a shifted sum of finite free
objects (`DerivedCategory.isShiftSum_of_isGE_of_isLE`), the truncation triangles splitting because
the unit is projective. On shifts of the unit, `Fib_s` is bijective on morphisms: both sides
vanish in nonzero degrees by projectivity, and in degree zero they are `ℚ̄_ℓ`. Hence `Fib_s` is
fully faithful (`DerivedCategory.homBijective_of_isShiftSum`), and its essential image is the
bounded complexes with finite-dimensional cohomology
(`ProEtale.CondensedRing.exists_fiberFunctor_point`, blueprint
`lemma-perfect-complexes-geometric-point`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]

/-- The base point `Spec k` is a noetherian topological space. -/
instance noetherianSpace_point : TopologicalSpace.NoetherianSpace (point k).left :=
  inferInstanceAs (TopologicalSpace.NoetherianSpace (Spec (.of k)))

variable [IsSepClosed k]

/-- For `k` separably closed, the unit of `Mod_{ℚ̲̄_ℓ,s}` is projective. -/
instance projective_tensorUnit_pointMod : Projective (𝟙_ (PointMod ℓ k)) :=
  projective_regular_of_isSepClosed (k := k) _

/-- The scalars `ℚ̄_ℓ` acting on the unit of `Mod_{ℚ̲̄_ℓ,s}`, as a ring homomorphism to the
opposite of its endomorphism ring, from the universe `u + 1` copy of `ℚ̄_ℓ`. -/
noncomputable def pointScalarsOp :
    ULift.{u + 1} (PadicAlgCl ℓ) →+* (End (𝟙_ (PointMod ℓ k)))ᵐᵒᵖ :=
  ((pointUnitEndRingHom ℓ k).toOpposite fun x y ↦ by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]).comp
      ULift.ringEquiv.toRingHom

/-- The global sections `Γ = Hom(ℚ̲̄_ℓ,s, -) : Mod_{ℚ̲̄_ℓ,s} ⥤ Mod_{ℚ̄_ℓ}` over the point. -/
noncomputable def pointSections :
    PointMod ℓ k ⥤ ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ℓ)) :=
  preadditiveCoyonedaObj (𝟙_ (PointMod ℓ k)) ⋙ ModuleCat.restrictScalars (pointScalarsOp ℓ k)

instance : (pointSections ℓ k).Additive := by
  unfold pointSections
  infer_instance

instance : PreservesFiniteLimits (pointSections ℓ k) := by
  unfold pointSections
  infer_instance

instance : PreservesFiniteColimits (pointSections ℓ k) := by
  unfold pointSections
  infer_instance

/-- The identity of the unit, as a global section of the unit. -/
noncomputable def pointSectionsUnit : (pointSections ℓ k).obj (𝟙_ (PointMod ℓ k)) :=
  𝟙 (𝟙_ (PointMod ℓ k))

omit [IsSepClosed k] in
/-- The scalar `a` acts on the global sections of the unit by the endomorphism `a` of the unit. -/
lemma smul_pointSectionsUnit (a : ULift.{u + 1} (PadicAlgCl ℓ)) :
    a • pointSectionsUnit ℓ k = (pointUnitEndRingHom ℓ k a.down).asHom :=
  Category.comp_id _

/-- The global sections of the unit of `Mod_{ℚ̲̄_ℓ,s}` are `ℚ̄_ℓ`. -/
noncomputable def pointSectionsUnitIso :
    ModuleCat.of _ (ULift.{u + 1} (PadicAlgCl ℓ)) ≅ (pointSections ℓ k).obj (𝟙_ (PointMod ℓ k)) :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ (pointSectionsUnit ℓ k)) (by
    have h : ⇑(LinearMap.toSpanSingleton (ULift.{u + 1} (PadicAlgCl ℓ)) _
        (pointSectionsUnit ℓ k)) = (fun a ↦ (pointUnitEndRingHom ℓ k a).asHom) ∘ ULift.down := by
      ext1 a
      exact smul_pointSectionsUnit ℓ k a
    rw [h]
    exact (End.homEquiv.bijective.comp
      (bijective_pointUnitEndRingHom ℓ k)).comp Equiv.ulift.bijective)).toModuleIso

/-- The global sections functor is bijective on the endomorphisms of the unit: every
endomorphism of the `ℚ̄_ℓ`-vector space `Γ(ℚ̲̄_ℓ,s) = ℚ̄_ℓ` is the composition with an endomorphism
of the unit. -/
lemma bijective_pointSections_map_unit :
    Function.Bijective (fun φ : 𝟙_ (PointMod ℓ k) ⟶ 𝟙_ (PointMod ℓ k) ↦
      (pointSections ℓ k).map φ) := by
  refine ⟨fun φ ψ h ↦ ?_, fun T ↦ ⟨T.hom (pointSectionsUnit ℓ k), ?_⟩⟩
  · have := congrArg (fun T ↦ T.hom (pointSectionsUnit ℓ k)) h
    change 𝟙 _ ≫ φ = 𝟙 _ ≫ ψ at this
    simpa using this
  · ext x
    obtain ⟨a, rfl⟩ := (End.homEquiv.bijective.comp
      (bijective_pointUnitEndRingHom ℓ k)).2 x
    change ((pointSections ℓ k).map (T.hom (pointSectionsUnit ℓ k))).hom
        (pointUnitEndRingHom ℓ k a).asHom = T.hom (pointUnitEndRingHom ℓ k a).asHom
    rw [← smul_pointSectionsUnit ℓ k (ULift.up a), map_smul, map_smul]
    congr 1

variable [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-- **The point category, evaluated**: the functor `Fib_s : Dᵇc(s)⟦ℚ̲̄_ℓ⟧ ⥤ D(ℚ̄_ℓ)` induced by the
exact global sections functor over the point. -/
noncomputable def pointFiberFunctor :
    Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ℓ))) :=
  (boundedConstructible _).ι ⋙ (pointSections ℓ k).mapDerivedCategory

noncomputable instance : (pointFiberFunctor ℓ k).CommShift ℤ := by
  unfold pointFiberFunctor
  infer_instance

instance : (pointFiberFunctor ℓ k).Additive := by
  unfold pointFiberFunctor
  infer_instance

/-- `Fib_s` sends the unit `ℚ̲̄_ℓ,s` to `ℚ̄_ℓ[0]`. -/
noncomputable def pointFiberFunctorUnitIso :
    (pointFiberFunctor ℓ k).obj (𝟙_ _) ≅
      (DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of _ (ULift.{u + 1} (PadicAlgCl ℓ))) :=
  (pointSections ℓ k).mapDerivedCategory.mapIso
      ((DerivedCategory.quotientCompQhIso (PointMod ℓ k)).app
        (𝟙_ (CochainComplex (PointMod ℓ k) ℤ))) ≪≫
    ((pointSections ℓ k).mapDerivedCategorySingleFunctor 0).app (𝟙_ (PointMod ℓ k)) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (pointSectionsUnitIso ℓ k).symm

/-- An object of `Mod_{ℚ̲̄_ℓ,s}` is *finite free* if it is a finite direct sum of copies of the
unit. -/
def pointFiniteFree : ObjectProperty (PointMod ℓ k) := fun X ↦
  ∃ n : ℕ, Nonempty (X ≅ ⨁ fun _ : Fin n ↦ 𝟙_ (PointMod ℓ k))

instance : (pointFiniteFree ℓ k).IsClosedUnderIsomorphisms :=
  ⟨fun e ⟨n, ⟨e'⟩⟩ ↦ ⟨n, ⟨e.symm ≪≫ e'⟩⟩⟩

omit [IsSepClosed k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
lemma pointFiniteFree_of_isZero {X : PointMod ℓ k} (hX : IsZero X) : pointFiniteFree ℓ k X :=
  ⟨0, ⟨hX.iso (isZero_biproduct_fin_zero _)⟩⟩

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
lemma projective_of_pointFiniteFree {X : PointMod ℓ k} (hX : pointFiniteFree ℓ k X) :
    Projective X := by
  obtain ⟨n, ⟨e⟩⟩ := hX
  let Q : ObjectProperty (PointMod ℓ k) := fun X ↦ Projective X
  have : Q.IsClosedUnderIsomorphisms := ⟨fun e h ↦ Projective.of_iso e h⟩
  have h := Q.prop_biproduct_fin (fun X hX ↦ ⟨fun _ _ _ ↦ ⟨0, hX.eq_of_src _ _⟩⟩)
    (fun X Y (hX : Projective X) (hY : Projective Y) ↦ (inferInstance : Projective (X ⊞ Y)))
    (inferInstance : Projective (𝟙_ (PointMod ℓ k))) n
  exact Projective.of_iso e.symm h

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsSepClosed k]

/-- On the shifts of the unit, the functor induced by the global sections over the point is
bijective on morphisms: both sides vanish in nonzero degrees, the unit being projective, and in
degree zero both sides are `ℚ̄_ℓ`. -/
theorem homBijective_pointSections_unit (b : ℤ) :
    (pointSections ℓ k).mapDerivedCategory.HomBijective
      ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ (PointMod ℓ k)))
      ((shiftFunctor _ b).obj ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ (PointMod ℓ k)))) := by
  let F := (pointSections ℓ k).mapDerivedCategory
  let S := DerivedCategory.singleFunctor (PointMod ℓ k) 0
  let S' := DerivedCategory.singleFunctor (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ℓ))) 0
  let e := (pointSections ℓ k).mapDerivedCategorySingleFunctor 0
  by_cases hb : b = 0
  · subst hb
    refine Functor.HomBijective.of_iso_right ?_ ((shiftFunctorZero _ ℤ).app _).symm
    have hS := (Functor.FullyFaithful.ofFullyFaithful S).map_bijective (𝟙_ _) (𝟙_ _)
    have hS' := (Functor.FullyFaithful.ofFullyFaithful S').map_bijective
      ((pointSections ℓ k).obj (𝟙_ _)) ((pointSections ℓ k).obj (𝟙_ _))
    have hconj : Function.Bijective (fun χ : S'.obj ((pointSections ℓ k).obj (𝟙_ _)) ⟶
        S'.obj ((pointSections ℓ k).obj (𝟙_ _)) ↦
          e.hom.app (𝟙_ (PointMod ℓ k)) ≫ χ ≫ e.inv.app (𝟙_ (PointMod ℓ k))) :=
      ((e.app (𝟙_ (PointMod ℓ k))).homCongr (e.app (𝟙_ (PointMod ℓ k)))).symm.bijective
    have hcomp : (fun φ ↦ F.map φ) ∘ (fun φ : 𝟙_ (PointMod ℓ k) ⟶ 𝟙_ _ ↦ S.map φ) =
        (fun χ ↦ e.hom.app (𝟙_ (PointMod ℓ k)) ≫ χ ≫ e.inv.app (𝟙_ (PointMod ℓ k))) ∘
          (fun φ ↦ S'.map φ) ∘ (fun φ ↦ (pointSections ℓ k).map φ) := by
      ext1 φ
      have := e.hom.naturality φ
      simp only [Functor.comp_map] at this
      simp only [Function.comp_apply]
      rw [← Category.assoc, ← this, Category.assoc, Iso.hom_inv_id_app]
      exact (Category.comp_id _).symm
    exact (Function.Bijective.of_comp_iff _ hS).1
      (hcomp ▸ hconj.comp (hS'.comp (bijective_pointSections_map_unit ℓ k)))
  · have h₂ : Subsingleton (F.obj (S.obj (𝟙_ (PointMod ℓ k))) ⟶
        F.obj ((shiftFunctor _ b).obj (S.obj (𝟙_ (PointMod ℓ k))))) := by
      have := DerivedCategory.subsingleton_singleFunctor_hom_shift
        ((pointSections ℓ k).obj (𝟙_ (PointMod ℓ k))) ((pointSections ℓ k).obj (𝟙_ _)) hb
      exact @Equiv.subsingleton _ _ ((e.app (𝟙_ (PointMod ℓ k))).homCongr
        ((F.commShiftIso b).app _ ≪≫ (shiftFunctor _ b).mapIso (e.app (𝟙_ (PointMod ℓ k))))) this
    have h₁ := DerivedCategory.subsingleton_singleFunctor_hom_shift (𝟙_ (PointMod ℓ k))
      (𝟙_ (PointMod ℓ k)) hb
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- On the shifts of finite free objects, the functor induced by the global sections over the
point is bijective on morphisms. -/
theorem homBijective_pointSections_finiteFree {X Y : PointMod ℓ k} (hX : pointFiniteFree ℓ k X)
    (hY : pointFiniteFree ℓ k Y) (b : ℤ) :
    (pointSections ℓ k).mapDerivedCategory.HomBijective
      ((DerivedCategory.singleFunctor _ 0).obj X)
      ((shiftFunctor _ b).obj ((DerivedCategory.singleFunctor _ 0).obj Y)) := by
  let F := (pointSections ℓ k).mapDerivedCategory
  let S := DerivedCategory.singleFunctor (PointMod ℓ k) 0
  have := preservesBinaryBiproducts_of_preservesBiproducts S
  have (b : ℤ) := preservesBinaryBiproducts_of_preservesBiproducts (S ⋙ shiftFunctor _ b)
  let QA : ObjectProperty (PointMod ℓ k) := fun X ↦
    ∀ b : ℤ, F.HomBijective (S.obj X) ((shiftFunctor _ b).obj (S.obj (𝟙_ _)))
  have : QA.IsClosedUnderIsomorphisms := ⟨fun e h b ↦ (h b).of_iso_left (S.mapIso e)⟩
  have hA (n : ℕ) : QA (⨁ fun _ : Fin n ↦ 𝟙_ (PointMod ℓ k)) :=
    QA.prop_biproduct_fin (fun _ hX b ↦ .of_isZero_left (S.map_isZero hX))
      (fun X₁ X₂ h₁ h₂ b ↦ ((h₁ b).biprod_left (h₂ b)).of_iso_left (S.mapBiprod X₁ X₂).symm)
      (homBijective_pointSections_unit ℓ k) n
  let QB : ObjectProperty (PointMod ℓ k) := fun Y ↦ ∀ (n : ℕ) (b : ℤ),
    F.HomBijective (S.obj (⨁ fun _ : Fin n ↦ 𝟙_ (PointMod ℓ k))) ((shiftFunctor _ b).obj (S.obj Y))
  have : QB.IsClosedUnderIsomorphisms :=
    ⟨fun e h n b ↦ (h n b).of_iso_right ((shiftFunctor _ b).mapIso (S.mapIso e))⟩
  have hB (m : ℕ) : QB (⨁ fun _ : Fin m ↦ 𝟙_ (PointMod ℓ k)) :=
    QB.prop_biproduct_fin
      (fun _ hY n b ↦ .of_isZero_right ((shiftFunctor _ b).map_isZero (S.map_isZero hY)))
      (fun Y₁ Y₂ h₁ h₂ n b ↦ ((h₁ n b).biprod_right (h₂ n b)).of_iso_right
        ((S ⋙ shiftFunctor _ b).mapBiprod Y₁ Y₂).symm)
      (fun n b ↦ hA n b) m
  obtain ⟨n, ⟨eX⟩⟩ := hX
  obtain ⟨m, ⟨eY⟩⟩ := hY
  exact ((hB m n b).of_iso_left (S.mapIso eX.symm)).of_iso_right
    ((shiftFunctor _ b).mapIso (S.mapIso eY.symm))

variable [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-- Every object of `Dᵇc(s)⟦ℚ̲̄_ℓ⟧` is a shifted sum of finite free objects: it is bounded with
finite free cohomology sheaves, and the truncation triangles split. -/
lemma isShiftSum_boundedConstructible_point
    (K : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    DerivedCategory.IsShiftSum (pointFiniteFree ℓ k) K.obj := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, -⟩ := K.property
  refine DerivedCategory.isShiftSum_of_isGE_of_isLE (fun X hX ↦ pointFiniteFree_of_isZero ℓ k hX)
    (fun X hX ↦ projective_of_pointFiniteFree ℓ k hX) ha hb fun q ↦ ?_
  obtain ⟨n, ⟨e⟩⟩ := isFiniteFree_upperStar_homology ℓ (Field.toIsField k)
    IsField.isSepClosed_toField K q (𝟙 _)
  exact ⟨n, ⟨((upperStarId _ _).app _).symm ≪≫ e⟩⟩

/-- `Fib_s` is bijective on morphisms. -/
theorem bijective_pointFiberFunctor_map
    (K L : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Function.Bijective (fun φ : K ⟶ L ↦ (pointFiberFunctor ℓ k).map φ) :=
  (DerivedCategory.homBijective_of_isShiftSum
    (fun _ _ hX hY b ↦ homBijective_pointSections_finiteFree ℓ k hX hY b)
    (isShiftSum_boundedConstructible_point ℓ k K)
    (isShiftSum_boundedConstructible_point ℓ k L)).comp
    ((ObjectProperty.fullyFaithfulι _).map_bijective K L)

/-- The images under `Fib_s` are bounded with finite-dimensional cohomology. -/
lemma boundedFiniteCohomology_pointFiberFunctor_obj
    (K : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    DerivedCategory.boundedFiniteCohomology _ ((pointFiberFunctor ℓ k).obj K) := by
  let F := (pointSections ℓ k).mapDerivedCategory
  let S := DerivedCategory.singleFunctor (PointMod ℓ k) 0
  let B := DerivedCategory.boundedFiniteCohomology (ULift.{u + 1} (PadicAlgCl ℓ))
  let Q : ObjectProperty (DerivedCategory (PointMod ℓ k)) := fun M ↦ B (F.obj M)
  have : Q.IsClosedUnderIsomorphisms := ⟨fun e h ↦ B.prop_of_iso (F.mapIso e) h⟩
  have hb (M₁ M₂ : DerivedCategory (PointMod ℓ k)) (h₁ : Q M₁) (h₂ : Q M₂) : Q (M₁ ⊞ M₂) := by
    have := preservesBinaryBiproducts_of_preservesBiproducts F
    exact B.prop_of_iso (F.mapBiprod M₁ M₂).symm (B.ext_of_isTriangulatedClosed₂ _
      (Pretriangulated.binaryBiproductTriangle_distinguished _ _) h₁ h₂)
  refine (isShiftSum_boundedConstructible_point ℓ k K).prop Q
    (fun M hM ↦ B.prop_of_isZero (F.map_isZero hM)) hb
    (fun M n h ↦ B.prop_of_iso ((F.commShiftIso n).app M).symm (B.le_shift n _ h))
    (fun X hX ↦ ?_)
  let Q' : ObjectProperty (PointMod ℓ k) := fun X ↦ Q (S.obj X)
  have : Q'.IsClosedUnderIsomorphisms := ⟨fun e h ↦ Q.prop_of_iso (S.mapIso e) h⟩
  have := preservesBinaryBiproducts_of_preservesBiproducts S
  obtain ⟨n, ⟨e⟩⟩ := hX
  exact Q'.prop_of_iso e.symm (Q'.prop_biproduct_fin
    (fun X hX ↦ B.prop_of_isZero (F.map_isZero (S.map_isZero hX)))
    (fun X₁ X₂ h₁ h₂ ↦ Q.prop_of_iso (S.mapBiprod X₁ X₂).symm (hb _ _ h₁ h₂))
    (B.prop_of_iso (pointFiberFunctorUnitIso ℓ k).symm
      (DerivedCategory.boundedFiniteCohomology_singleFunctor _)) n)

omit [Fact (ringChar k).Prime] in
/-- Every bounded complex of `ℚ̄_ℓ`-vector spaces with finite-dimensional cohomology is in the
essential image of `Fib_s`: it is a finite direct sum of shifts of `ℚ̄_ℓ[0] = Fib_s(ℚ̲̄_ℓ,s)`. -/
lemma exists_pointFiberFunctor_obj_iso
    {M : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ℓ)))}
    (hM : DerivedCategory.boundedFiniteCohomology _ M) :
    ∃ K, Nonempty ((pointFiberFunctor ℓ k).obj K ≅ M) := by
  let G := pointFiberFunctor ℓ k
  have : G.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive G
  have := preservesBinaryBiproducts_of_preservesBiproducts G
  have : HasBinaryBiproducts (DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ℓ)))) :=
    inferInstance
  let Q : ObjectProperty (DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ℓ)))) :=
    fun M ↦ ∃ K, Nonempty (G.obj K ≅ M)
  have : Q.IsClosedUnderIsomorphisms := ⟨fun e ⟨K, ⟨e'⟩⟩ ↦ ⟨K, ⟨e' ≪≫ e⟩⟩⟩
  exact DerivedCategory.prop_of_boundedFiniteCohomology_of_field Q
    (fun X hX ↦ ⟨0, ⟨(G.map_isZero (isZero_zero _)).iso hX⟩⟩)
    (fun X Y ⟨KX, ⟨eX⟩⟩ ⟨KY, ⟨eY⟩⟩ ↦ ⟨KX ⊞ KY, ⟨G.mapBiprod KX KY ≪≫ biprod.mapIso eX eY⟩⟩)
    (fun X n ⟨K, ⟨e⟩⟩ ↦ ⟨(shiftFunctor _ n).obj K,
      ⟨(G.commShiftIso n).app K ≪≫ (shiftFunctor _ n).mapIso e⟩⟩)
    ⟨𝟙_ _, ⟨pointFiberFunctorUnitIso ℓ k⟩⟩ hM

/-- **The point category, evaluated** (blueprint `lemma-perfect-complexes-geometric-point`): for `k`
separably closed, evaluation at the geometric point `s = Spec k` is an exact equivalence
`Fib_s : Dᵇc(s)⟦ℚ̲̄_ℓ⟧ ≃ Dᵇ_fd(ℚ̄_ℓ)` onto the bounded complexes of `ℚ̄_ℓ`-vector spaces with
finite-dimensional cohomology; it sends the unit `ℚ̲̄_ℓ,s` to `ℚ̄_ℓ[0]`. -/
theorem exists_fiberFunctor_point :
    ∃ (G : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
        DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ℓ)))) (_ : G.CommShift ℤ),
      G.Additive ∧ Nonempty G.FullyFaithful ∧
      (∀ P, DerivedCategory.boundedFiniteCohomology _ (G.obj P)) ∧
      (∀ M, DerivedCategory.boundedFiniteCohomology _ M → ∃ P, Nonempty (G.obj P ≅ M)) ∧
      Nonempty (G.obj (𝟙_ _) ≅ (DerivedCategory.singleFunctor _ 0).obj
        (ModuleCat.of _ (ULift.{u + 1} (PadicAlgCl ℓ)))) := by
  have : (pointFiberFunctor ℓ k).Full :=
    ⟨fun f ↦ (bijective_pointFiberFunctor_map ℓ k _ _).2 f⟩
  have : (pointFiberFunctor ℓ k).Faithful :=
    ⟨fun h ↦ (bijective_pointFiberFunctor_map ℓ k _ _).1 h⟩
  exact ⟨pointFiberFunctor ℓ k, inferInstance, inferInstance,
    ⟨Functor.FullyFaithful.ofFullyFaithful _⟩, boundedFiniteCohomology_pointFiberFunctor_obj ℓ k,
    fun _ hM ↦ exists_pointFiberFunctor_obj_iso ℓ k hM, ⟨pointFiberFunctorUnitIso ℓ k⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
