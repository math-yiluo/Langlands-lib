/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Field.ULift
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.SheafQuasiCompact
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheaf

/-!
# The constant sheaf `Λ_X` of a nonarchimedean ring on the pro-étale site

Let `Λ` be a commutative ring with an ultrametric norm, for instance a finite extension `E` of
`ℚ_ℓ` inside `ℚ̄_ℓ` with the restricted norm, or its ring of integers `𝒪_E`. Following
Bhatt–Scholze (*The pro-étale topology for schemes*, §6.8), the constructible `E`-sheaves of the
blueprint (`definition-weil-structure`) are modules over the
pro-étale sheaf `E_X : U ↦ C(U, E)` of continuous `E`-valued functions. This file constructs
`Λ_X` (`AlgebraicGeometry.ProEtale.fieldConstantSheaf Λ X`) for any such `Λ`: it is the
restriction to the small pro-étale site of `X` of the presheaf `U ↦ C(U, Λ)` on all schemes,
which is an fpqc sheaf.

This file and the others in `WeilConjectures.SixFunctors.ProEtale.FieldCoefficient` are the
counterparts, for the coefficient field `Λ`, of the files in
`WeilConjectures.SixFunctors.ProEtale.Adic`, which treat `ℚ̄_ℓ = PadicAlgCl ℓ`, and follow them
closely. For `ℚ̄_ℓ`, which is not locally compact, the sheaf of Bhatt–Scholze is that of the
*locally finite* continuous functions (`PadicAlgCl.locallyFiniteFunctions`); for a finite
extension `E` of `ℚ_ℓ` every continuous function is locally finite, and the two descriptions
agree. To keep the proofs of the `ℚ̄_ℓ` case, the sections are packaged as the subalgebra
`AlgebraicGeometry.fieldFunctions Λ U = ⊤` of `C(U, Λ)`.

## Main definitions

- `AlgebraicGeometry.FieldCoefficients`: the coefficient category, modules over `Λ`, lifted to
  the universe of the sites.
- `AlgebraicGeometry.fieldFunctions`: the continuous functions `T → Λ`, as a subalgebra.
- `AlgebraicGeometry.fieldFunctionsPresheaf`: the presheaf `U ↦ C(U, Λ)` on all schemes, an
  fpqc sheaf (`AlgebraicGeometry.isSheaf_fpqcTopology_fieldFunctionsPresheaf`).
- `AlgebraicGeometry.ProEtale.fieldConstantSheaf`: the constant sheaf `Λ_X`.
- `AlgebraicGeometry.ProEtale.fieldConstantSheafLowerStarIso`: for an isomorphism `e : X ≅ Y`,
  `e_* Λ_X ≅ Λ_Y`.

## Main results

- `AlgebraicGeometry.ProEtale.not_isZero_fieldConstantSheaf`: `Λ_X` is nonzero on a nonempty
  scheme.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite Topology

namespace AlgebraicGeometry

section FieldFunctions

variable (Λ : Type) [NormedCommRing Λ] (T : Type*) [TopologicalSpace T]

/-- The continuous functions `T → Λ`, as a `Λ`-subalgebra (all) of `C(T, Λ)`. They are the
sections over `T` of the constant sheaf `Λ_X`; they play the role of the locally finite
functions `PadicAlgCl.locallyFiniteFunctions` of the `ℚ̄_ℓ` case, and agree with them for a
finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ`. -/
abbrev fieldFunctions : Subalgebra Λ C(T, Λ) := ⊤

variable {Λ T}

/-- Every continuous function is a section of `Λ_X`. -/
lemma mem_fieldFunctions (f : C(T, Λ)) : f ∈ fieldFunctions Λ T :=
  Algebra.mem_top

/-- The constant functions are sections of `Λ_X`. -/
lemma const_mem_fieldFunctions (c : Λ) :
    ContinuousMap.const T c ∈ fieldFunctions Λ T :=
  Algebra.mem_top

variable {T' : Type*} [TopologicalSpace T']

/-- Precomposition with a continuous map preserves the sections. -/
lemma comp_mem_fieldFunctions {f : C(T, Λ)} (_hf : f ∈ fieldFunctions Λ T) (g : C(T', T)) :
    f.comp g ∈ fieldFunctions Λ T' :=
  Algebra.mem_top

variable (Λ) in
/-- Precomposition with a continuous map `g : T' → T`, as a `Λ`-linear map. -/
noncomputable def fieldFunctionsComp (g : C(T', T)) :
    fieldFunctions Λ T →ₗ[Λ] fieldFunctions Λ T' where
  toFun f := ⟨f.1.comp g, comp_mem_fieldFunctions f.2 g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma fieldFunctionsComp_apply_coe (g : C(T', T)) (f : fieldFunctions Λ T) :
    ((fieldFunctionsComp Λ g f : fieldFunctions Λ T') : C(T', Λ)) =
      (f : C(T, Λ)).comp g :=
  rfl

end FieldFunctions

/-- A subfield `E` of `ℚ̄_ℓ`, for instance a finite extension of `ℚ_ℓ`, with the norm restricted
from `ℚ̄_ℓ`, is ultrametric: it is a coefficient field `Λ = E` of the constructions of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient`. -/
instance _root_.PadicAlgCl.isUltrametricDist_intermediateField {l : ℕ} [Fact l.Prime]
    (E : IntermediateField ℚ_[l] (PadicAlgCl l)) : IsUltrametricDist E :=
  IsUltrametricDist.subtype _


/-- The coefficients of `Λ`-adic pro-étale sheaves: modules over `Λ`, lifted to
`Type (u + 1)`, the universe of the `Hom`-types of sheaves on the sites of `Scheme.{u}`. The
topology of `Λ` does not enter the coefficient category: it enters through the constant sheaf
`AlgebraicGeometry.ProEtale.fieldConstantSheaf`. -/
abbrev FieldCoefficients (Λ : Type) [NormedCommRing Λ] : Type (u + 2) :=
  ModuleCat.{u + 1} (ULift.{u + 1} Λ)

namespace FieldCoefficients

variable (Λ : Type) [NormedCommRing Λ]

/-- The underlying `Λ`-vector space of a module over `ULift Λ`, by restriction of scalars
along `Λ ≃ ULift Λ`. -/
noncomputable abbrev toModuleCat :
    FieldCoefficients.{u} Λ ⥤ ModuleCat.{u + 1} Λ :=
  ModuleCat.restrictScalars (ULift.ringEquiv (R := Λ)).symm.toRingHom

variable {Λ}

/-- An isomorphism of modules over `ULift Λ` as a `Λ`-linear isomorphism of the
underlying `Λ`-vector spaces. -/
noncomputable def linearEquivOfIso {M N : FieldCoefficients.{u} Λ} (e : M ≅ N) :
    (toModuleCat Λ).obj M ≃ₗ[Λ] (toModuleCat Λ).obj N :=
  ((toModuleCat Λ).mapIso e).toLinearEquiv

/-- A `Λ`-linear map, lifted to a `ULift Λ`-linear map of the universe lifts. -/
noncomputable def uliftLinearMap {M N : Type*} [AddCommGroup M] [Module Λ M]
    [AddCommGroup N] [Module Λ N] (φ : M →ₗ[Λ] N) :
    ULift.{u + 1} M →ₗ[ULift.{u + 1} Λ] ULift.{u + 1} N where
  toFun x := ULift.up (φ x.down)
  map_add' x y := congrArg ULift.up (φ.map_add x.down y.down)
  map_smul' c x := congrArg ULift.up (φ.map_smul c.down x.down)

end FieldCoefficients

variable (Λ : Type) [NormedCommRing Λ]

open FieldCoefficients

/-- The presheaf `U ↦ C(U, Λ)` on all schemes, with restriction given by
precomposition with the underlying continuous maps. -/
@[simps]
noncomputable def fieldFunctionsPresheaf : Scheme.{u}ᵒᵖ ⥤ FieldCoefficients.{u} Λ where
  obj U := ModuleCat.of _ (ULift.{u + 1} (fieldFunctions Λ U.unop))
  map f := ModuleCat.ofHom (uliftLinearMap (fieldFunctionsComp Λ f.unop.base.hom))

/-- The presheaf of continuous maps to `ULift Λ` on `Scheme.{u}`, with values in
`Type (u + 1)`. -/
noncomputable abbrev fieldContinuousMapPresheaf : Scheme.{u}ᵒᵖ ⥤ Type (u + 1) :=
  continuousMapPresheaf (ULift.{u + 1} Λ)

/-- The continuous functions to `Λ`, as a subfunctor of the continuous maps to `ULift Λ` (all of
it). -/
noncomputable def fieldFunctionsSubfunctor : Subfunctor (fieldContinuousMapPresheaf.{u} Λ) where
  obj _ := Set.univ
  map _ _ _ := Set.mem_univ _

/-- The continuous functions to `Λ` form an fpqc sheaf
(`AlgebraicGeometry.isSheaf_fpqcTopology_continuousMapPresheaf`). -/
lemma isSheaf_fpqcTopology_fieldFunctionsSubfunctor :
    Presieve.IsSheaf Scheme.fpqcTopology (fieldFunctionsSubfunctor.{u} Λ).toFunctor :=
  ((fieldFunctionsSubfunctor Λ).isSheaf_iff ((isSheaf_iff_isSheaf_of_type _ _).1
    (isSheaf_fpqcTopology_continuousMapPresheaf (ULift.{u + 1} Λ)))).2
    fun _ _ _ ↦ Set.mem_univ _

/-- The presheaf of continuous functions to `Λ` is the subfunctor
`AlgebraicGeometry.fieldFunctionsSubfunctor` of the continuous maps to `ULift Λ`. -/
noncomputable def fieldFunctionsPresheafForgetIso :
    fieldFunctionsPresheaf.{u} Λ ⋙ forget (FieldCoefficients.{u} Λ) ≅
      (fieldFunctionsSubfunctor.{u} Λ).toFunctor :=
  NatIso.ofComponents (fun U ↦ Equiv.toIso
    { toFun x := ⟨⟨fun t ↦ ULift.up (x.down.1 t), continuous_uliftUp.comp x.down.1.continuous⟩,
        Set.mem_univ _⟩
      invFun s := ULift.up
        ⟨(ContinuousMap.mk ULift.down continuous_uliftDown).comp s.1, Algebra.mem_top⟩
      left_inv _ := rfl
      right_inv _ := rfl })
    fun _ ↦ by ext x; exact Subtype.ext (ContinuousMap.ext fun _ ↦ rfl)

/-- The presheaf `U ↦ C(U, Λ)` of continuous functions is a sheaf for the fpqc topology
(`AlgebraicGeometry.isSheaf_fpqcTopology_continuousMapPresheaf`). -/
theorem isSheaf_fpqcTopology_fieldFunctionsPresheaf :
    Presheaf.IsSheaf Scheme.fpqcTopology (fieldFunctionsPresheaf.{u} Λ) := by
  have : ReflectsLimitsOfSize.{u, u + 1} (forget (FieldCoefficients.{u} Λ)) :=
    reflectsLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  refine Presheaf.isSheaf_of_isSheaf_comp Scheme.fpqcTopology _
    (forget (FieldCoefficients.{u} Λ)) ((isSheaf_iff_isSheaf_of_type _ _).2 ?_)
  exact Presieve.isSheaf_iso _ (fieldFunctionsPresheafForgetIso Λ).symm
    (isSheaf_fpqcTopology_fieldFunctionsSubfunctor Λ)


namespace ProEtale

/-- The constant sheaf `Λ_X` on the small pro-étale site of `X`: the sections over a
weakly étale `U → X` are the continuous functions `U → Λ` (Bhatt–Scholze, §6.8). -/
noncomputable def fieldConstantSheaf (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) (FieldCoefficients.{u} Λ) :=
  ((Scheme.ProEt.forget X ⋙ Over.forget _).sheafPushforwardContinuous _ _
    Scheme.proetaleTopology).obj
    ⟨fieldFunctionsPresheaf Λ, .of_le Scheme.proetaleTopology_le_fpqcTopology <|
      isSheaf_fpqcTopology_fieldFunctionsPresheaf Λ⟩

/-- The sections of `Λ_X` over `U` are the continuous functions on `U`. -/
lemma fieldConstantSheaf_obj_obj (X : Scheme.{u}) (U : X.ProEt) :
    (fieldConstantSheaf Λ X).obj.obj (op U) =
      (fieldFunctionsPresheaf Λ).obj (op U.left) :=
  rfl

/-- The pushforward of the constant sheaf along an isomorphism `e : X ≅ Y` is the
constant sheaf: its sections over `V → Y` are the continuous functions on
`V ×_Y X`, which the canonical isomorphism `V ×_Y X ≅ V` identifies with those on `V`. -/
noncomputable def fieldConstantSheafLowerStarIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    (e.hom)_*[FieldCoefficients.{u} Λ].obj (fieldConstantSheaf Λ X) ≅
      fieldConstantSheaf Λ Y :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (show _ ≅ _ from
    (Functor.isoWhiskerRight (NatIso.op (overPullbackForgetIso e.hom))
      (fieldFunctionsPresheaf Λ)).symm)

/-- The restriction maps of `Λ_X` are the pullbacks of functions along the underlying
morphisms of schemes. -/
lemma fieldConstantSheaf_obj_map {X : Scheme.{u}} {U V : X.ProEtᵒᵖ} (f : U ⟶ V) :
    (fieldConstantSheaf Λ X).obj.map f = (fieldFunctionsPresheaf Λ).map f.unop.left.op :=
  rfl

lemma fieldConstantSheafLowerStarIso_inv_hom_app {X Y : Scheme.{u}} (e : X ≅ Y)
    (V : Y.ProEtᵒᵖ) :
    (fieldConstantSheafLowerStarIso Λ e).inv.hom.app V =
      (fieldFunctionsPresheaf Λ).map (pullback.fst V.unop.hom e.hom).op :=
  rfl

lemma fieldConstantSheafLowerStarIso_hom_hom_app {X Y : Scheme.{u}} (e : X ≅ Y)
    (V : Y.ProEtᵒᵖ) :
    (fieldConstantSheafLowerStarIso Λ e).hom.hom.app V =
      (fieldFunctionsPresheaf Λ).map
        (pullback.lift (𝟙 V.unop.left) (V.unop.hom ≫ e.inv) (by simp)).op := by
  rw [← cancel_mono ((fieldConstantSheafLowerStarIso Λ e).inv.hom.app V), ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id,
    fieldConstantSheafLowerStarIso_inv_hom_app, ← Functor.map_comp, ← op_comp,
    show pullback.fst _ _ ≫ pullback.lift _ _ _ = 𝟙 _ from
      pullback.hom_ext (by simp) (by simp [pullback.condition_assoc]), op_id,
    (fieldFunctionsPresheaf Λ).map_id]
  rfl

/-- The constant sheaf on a nonempty scheme is nonzero: the constant function `1` is a
nonzero global section. -/
theorem not_isZero_fieldConstantSheaf (X : Scheme.{u}) [Nonempty X] [Nontrivial Λ] :
    ¬ IsZero (fieldConstantSheaf Λ X) := by
  intro h
  -- the sections over the terminal object `X` of the pro-étale site
  let T : X.ProEt := Scheme.ProEt.mk (𝟙 X)
  have h' : IsZero ((fieldConstantSheaf Λ X).obj.obj (op T)) :=
    ((evaluation _ _).obj (op T)).map_isZero ((sheafToPresheaf _ _).map_isZero h)
  have h1 : (ULift.up ⟨ContinuousMap.const _ 1, const_mem_fieldFunctions 1⟩ :
      ULift.{u + 1} (fieldFunctions Λ T.left)) = 0 :=
    (ModuleCat.isZero_iff_subsingleton.1 h').elim _ _
  obtain ⟨x⟩ := ‹Nonempty X›
  have := congrArg (fun f : ULift.{u + 1} (fieldFunctions Λ T.left) ↦
    (f.down : C(T.left, Λ)) x) h1
  simp at this

end ProEtale

end AlgebraicGeometry
