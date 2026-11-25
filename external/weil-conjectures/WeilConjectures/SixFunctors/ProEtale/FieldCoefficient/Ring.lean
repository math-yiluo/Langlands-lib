/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Internal.Module
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal

/-!
# The constant sheaf is a sheaf of rings

This is the counterpart, for a commutative coefficient ring `Λ` with an ultrametric norm (the
cases of interest being a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` and its ring of integers
`𝒪_E`), of
`WeilConjectures.SixFunctors.ProEtale.Adic.Ring`, which treats `ℚ̄_ℓ`,
with the same proofs; the constant sheaf `Λ_X : U ↦ C(U, Λ)` is that of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstantSheaf`.

The sections of the constant sheaf `Λ_X = AlgebraicGeometry.ProEtale.fieldConstantSheaf`
over `U` are the continuous functions `U → Λ`, a `Λ`-algebra under pointwise
multiplication, and the restriction maps are algebra homomorphisms. Hence `Λ_X` is a monoid
object of the monoidal category of sheaves of `Λ`-modules on the pro-étale site of `X`
(Bhatt–Scholze, §6.8): a sheaf of rings. Its multiplication `Λ_X ⊗ Λ_X ⟶ Λ_X` restricts to
the pointwise multiplication of functions on the presheaf tensor product.

For a morphism `g : W ⟶ V` the comparison `Λ_V ⟶ g_* Λ_W`, pulling back functions, is a
morphism of sheaves of rings
(`AlgebraicGeometry.ProEtale.isMonHom_fieldConstantSheafToLowerStar`), so that its adjoint
`g^* Λ_V ≅ Λ_W` is an isomorphism of sheaves of rings.

## Main definitions

- `AlgebraicGeometry.ProEtale.fieldConstantSheaf.monObj`: the ring structure on `Λ_X`.

## Main results

- `AlgebraicGeometry.ProEtale.isMonHom_fieldConstantSheafToLowerStar`: pulling back functions is
  a morphism of sheaves of rings.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

namespace AlgebraicGeometry

variable (Λ : Type) [NormedCommRing Λ] [IsUltrametricDist Λ] {T T' : Type*} [TopologicalSpace T]
  [TopologicalSpace T']

/-- Precomposition with a continuous map `g : T' → T`, as a homomorphism of `Λ`-algebras of
continuous functions. -/
noncomputable def fieldFunctionsCompAlgHom (g : C(T', T)) :
    fieldFunctions Λ T →ₐ[Λ] fieldFunctions Λ T' where
  toFun f := ⟨f.1.comp g, comp_mem_fieldFunctions f.2 g⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

end AlgebraicGeometry

namespace AlgebraicGeometry

variable (Λ : Type) [NormedCommRing Λ] [IsUltrametricDist Λ]

open FieldCoefficients

namespace FieldCoefficients

/-- The `ULift Λ`-algebra structure on the universe lift of a `Λ`-algebra. -/
noncomputable instance uliftAlgebra (B : Type*) [Ring B] [Algebra Λ B] :
    Algebra (ULift.{u + 1} Λ) (ULift.{u + 1} B) :=
  Algebra.compHom _ (ULift.ringEquiv (R := Λ)).toRingHom

variable {Λ} in
/-- A homomorphism of `Λ`-algebras, lifted to a homomorphism of `ULift Λ`-algebras of the
universe lifts. -/
noncomputable def uliftAlgHom {B B' : Type*} [Ring B] [Algebra Λ B] [Ring B']
    [Algebra Λ B'] (φ : B →ₐ[Λ] B') :
    ULift.{u + 1} B →ₐ[ULift.{u + 1} Λ] ULift.{u + 1} B' where
  toFun x := ULift.up (φ x.down)
  map_one' := congrArg ULift.up φ.map_one
  map_mul' x y := congrArg ULift.up (φ.map_mul x.down y.down)
  map_zero' := congrArg ULift.up φ.map_zero
  map_add' x y := congrArg ULift.up (φ.map_add x.down y.down)
  commutes' c := congrArg ULift.up (φ.commutes c.down)

end FieldCoefficients

namespace ProEtale

variable (X : Scheme.{u})

/-- The presheaf of `ULift Λ`-algebras `U ↦ Λ_X(U)` of continuous functions. -/
@[simps]
noncomputable def fieldFunctionsAlgPresheaf :
    X.ProEtᵒᵖ ⥤ AlgCat.{u + 1} (ULift.{u + 1} Λ) where
  obj U := AlgCat.of _ (ULift.{u + 1} (fieldFunctions Λ U.unop.left))
  map f := AlgCat.ofHom (uliftAlgHom (fieldFunctionsCompAlgHom Λ f.unop.left.base.hom))

/-- The presheaf `Λ_X` as a monoid object of the category of presheaves of `ULift Λ`-modules,
from the pointwise algebra structures. -/
noncomputable def fieldFunctionsMonPresheaf :
    Mon (X.ProEtᵒᵖ ⥤ FieldCoefficients.{u} Λ) :=
  Monoidal.MonFunctorCategoryEquivalence.inverseObj
    (fieldFunctionsAlgPresheaf Λ X ⋙ ModuleCat.MonModuleEquivalenceAlgebra.inverse)

/-- The underlying presheaf of the monoid `AlgebraicGeometry.ProEtale.fieldFunctionsMonPresheaf`
is the underlying presheaf of `Λ_X`. -/
noncomputable def fieldFunctionsMonPresheafXIso :
    (fieldFunctionsMonPresheaf Λ X).X ≅ (fieldConstantSheaf Λ X).obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ by ext; rfl

/-- The underlying presheaf of `Λ_X` is a presheaf of rings. -/
noncomputable instance fieldConstantSheaf.monObjObj : MonObj (fieldConstantSheaf Λ X).obj :=
  .ofIso (fieldFunctionsMonPresheafXIso Λ X)

/-- **The constant sheaf is a sheaf of rings**: the ring structure induced from the
pointwise multiplication of continuous functions. -/
noncomputable instance fieldConstantSheaf.monObj : MonObj (fieldConstantSheaf Λ X) :=
  Sheaf.monObjOfPresheaf _

variable {Λ} in
omit [IsUltrametricDist Λ] in
/-- The multiplication of the underlying presheaf of `Λ_X` is the pointwise multiplication of
functions. -/
lemma fieldConstantSheaf_mul_app_tmul {U : X.ProEtᵒᵖ}
    (s t : (fieldConstantSheaf Λ X).obj.obj U) :
    (μ[(fieldConstantSheaf Λ X).obj]).app U (s ⊗ₜ t) = ULift.up (s.down * t.down) :=
  rfl

variable {Λ} in
omit [IsUltrametricDist Λ] in
/-- The unit of the underlying presheaf of `Λ_X` is the constant function `1`. -/
lemma fieldConstantSheaf_one_app {U : X.ProEtᵒᵖ} (r : ULift.{u + 1} Λ) :
    (η[(fieldConstantSheaf Λ X).obj]).app U r = ULift.up (algebraMap _ _ r.down) :=
  rfl

section LowerStar

open Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped Obj

variable {Λ} {V W : Scheme.{u}} (g : W ⟶ V)

omit [IsUltrametricDist Λ] in
lemma fieldConstantSheaf_ε_comp_map_one' (V : Scheme.{u}) :
    ε (sheafToPresheaf (Scheme.ProEt.topology V) (FieldCoefficients.{u} Λ)) ≫
        (sheafToPresheaf _ _).map η[fieldConstantSheaf Λ V] =
      η[(fieldConstantSheaf Λ V).obj] :=
  Sheaf.ε_comp_map_one _

omit [IsUltrametricDist Λ] in
lemma fieldConstantSheaf_μ_comp_map_mul' (V : Scheme.{u}) :
    «μ» (sheafToPresheaf (Scheme.ProEt.topology V) (FieldCoefficients.{u} Λ)) _ _ ≫
        (sheafToPresheaf _ _).map μ[fieldConstantSheaf Λ V] =
      μ[(fieldConstantSheaf Λ V).obj] :=
  Sheaf.μ_comp_map_mul _

/-- **Pulling back functions is a morphism of sheaves of rings** `Λ_V ⟶ g_* Λ_W`. On the
underlying presheaves both multiplications are pointwise multiplications of functions, the
multiplication of `g_* Λ_W` restricting to that of `Λ_W` along the comparison with the
presheaf tensor product
(`CategoryTheory.Functor.μ_sheafToPresheaf_comp_map_μ_sheafPushforwardContinuous`). -/
instance isMonHom_fieldConstantSheafToLowerStar :
    IsMonHom (fieldConstantSheafToLowerStar Λ g) := by
  have : IsMonHom ((sheafToPresheaf _ _).map (fieldConstantSheafToLowerStar Λ g)) :=
    { one_hom := by
        have h := Functor.ε_sheafToPresheaf_comp_map_ε_sheafPushforwardContinuous
          (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) (FieldCoefficients.{u} Λ)
          (Scheme.ProEt.topology V) (Scheme.ProEt.topology W)
        change (ε _ ≫ (sheafToPresheaf _ _).map η[fieldConstantSheaf Λ V]) ≫ _ =
          ε _ ≫ (sheafToPresheaf _ _).map
            (ε ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).sheafPushforwardContinuous
              _ _ _) ≫
              ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).sheafPushforwardContinuous
                _ _ _).map η[fieldConstantSheaf Λ W])
        rw [fieldConstantSheaf_ε_comp_map_one', Functor.map_comp, ← Category.assoc, h,
          Category.assoc]
        rw [show (sheafToPresheaf _ _).map (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g
            ).sheafPushforwardContinuous _ _ _).map η[fieldConstantSheaf Λ W]) =
            ((Functor.whiskeringLeft _ _ _).obj (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g
              ).op).map ((sheafToPresheaf _ _).map η[fieldConstantSheaf Λ W]) from rfl,
          ← Functor.map_comp, fieldConstantSheaf_ε_comp_map_one']
        ext U
        rfl
      mul_hom := by
        have h := Functor.μ_sheafToPresheaf_comp_map_μ_sheafPushforwardContinuous
          (A := FieldCoefficients.{u} Λ) (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g)
          (Scheme.ProEt.topology V) (Scheme.ProEt.topology W)
          (fieldConstantSheaf Λ W) (fieldConstantSheaf Λ W)
        change («μ» _ _ _ ≫ (sheafToPresheaf _ _).map μ[fieldConstantSheaf Λ V]) ≫ _ =
          _ ≫ «μ» _ _ _ ≫ (sheafToPresheaf _ _).map
            («μ» ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).sheafPushforwardContinuous
              _ _ _) _ _ ≫
              ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).sheafPushforwardContinuous
                _ _ _).map μ[fieldConstantSheaf Λ W])
        rw [fieldConstantSheaf_μ_comp_map_mul', Functor.map_comp, reassoc_of% h]
        rw [show (sheafToPresheaf _ _).map (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g
            ).sheafPushforwardContinuous _ _ _).map μ[fieldConstantSheaf Λ W]) =
            ((Functor.whiskeringLeft _ _ _).obj (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g
              ).op).map ((sheafToPresheaf _ _).map μ[fieldConstantSheaf Λ W]) from rfl,
          ← Functor.map_comp, fieldConstantSheaf_μ_comp_map_mul']
        refine NatTrans.ext (funext fun U ↦ ?_)
        exact ModuleCat.MonoidalCategory.tensor_ext fun s t ↦ rfl }
  exact Sheaf.isMonHom_of_isMonHom_map _

end LowerStar

end ProEtale

end AlgebraicGeometry
