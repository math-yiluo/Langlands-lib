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
public import WeilConjectures.SixFunctors.ProEtale.Adic.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal

/-!
# The constant `ℓ`-adic sheaf is a sheaf of rings

The sections of the constant `ℓ`-adic sheaf `ℚ̄_ℓ,X = AlgebraicGeometry.ProEtale.adicConstantSheaf`
over `U` are the locally finite continuous functions `U → ℚ̄_ℓ`, a `ℚ̄_ℓ`-algebra under pointwise
multiplication, and the restriction maps are algebra homomorphisms. Hence `ℚ̄_ℓ,X` is a monoid
object of the monoidal category of sheaves of `ℚ̄_ℓ`-modules on the pro-étale site of `X`
(Bhatt–Scholze, §6.8): a sheaf of rings. Its multiplication `ℚ̄_ℓ,X ⊗ ℚ̄_ℓ,X ⟶ ℚ̄_ℓ,X` restricts to
the pointwise multiplication of functions on the presheaf tensor product.

For a morphism `g : W ⟶ V` the comparison `ℚ̄_ℓ,V ⟶ g_* ℚ̄_ℓ,W`, pulling back functions, is a
morphism of sheaves of rings
(`AlgebraicGeometry.ProEtale.isMonHom_adicConstantSheafToLowerStar`), so that its adjoint
`g^* ℚ̄_ℓ,V ≅ ℚ̄_ℓ,W` is an isomorphism of sheaves of rings.

## Main definitions

- `AlgebraicGeometry.ProEtale.adicConstantSheaf.monObj`: the ring structure on `ℚ̄_ℓ,X`.

## Main results

- `AlgebraicGeometry.ProEtale.isMonHom_adicConstantSheafToLowerStar`: pulling back functions is
  a morphism of sheaves of rings.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] {T T' : Type*} [TopologicalSpace T] [TopologicalSpace T']

/-- Precomposition with a continuous map `g : T' → T`, as a homomorphism of `ℚ̄_ℓ`-algebras of
locally finite functions. -/
noncomputable def locallyFiniteFunctionsCompAlgHom (g : C(T', T)) :
    locallyFiniteFunctions l T →ₐ[PadicAlgCl l] locallyFiniteFunctions l T' where
  toFun f := ⟨f.1.comp g, comp_mem_locallyFiniteFunctions f.2 g⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

end PadicAlgCl

namespace AlgebraicGeometry

variable (l : ℕ) [Fact l.Prime]

open PadicAlgCl WeilCoefficients

namespace WeilCoefficients

/-- The `ULift ℚ̄_ℓ`-algebra structure on the universe lift of a `ℚ̄_ℓ`-algebra. -/
noncomputable instance uliftAlgebra (B : Type*) [Ring B] [Algebra (PadicAlgCl l) B] :
    Algebra (ULift.{u + 1} (PadicAlgCl l)) (ULift.{u + 1} B) :=
  Algebra.compHom _ (ULift.ringEquiv (R := PadicAlgCl l)).toRingHom

variable {l} in
/-- A homomorphism of `ℚ̄_ℓ`-algebras, lifted to a homomorphism of `ULift ℚ̄_ℓ`-algebras of the
universe lifts. -/
noncomputable def uliftAlgHom {B B' : Type*} [Ring B] [Algebra (PadicAlgCl l) B] [Ring B']
    [Algebra (PadicAlgCl l) B'] (φ : B →ₐ[PadicAlgCl l] B') :
    ULift.{u + 1} B →ₐ[ULift.{u + 1} (PadicAlgCl l)] ULift.{u + 1} B' where
  toFun x := ULift.up (φ x.down)
  map_one' := congrArg ULift.up φ.map_one
  map_mul' x y := congrArg ULift.up (φ.map_mul x.down y.down)
  map_zero' := congrArg ULift.up φ.map_zero
  map_add' x y := congrArg ULift.up (φ.map_add x.down y.down)
  commutes' c := congrArg ULift.up (φ.commutes c.down)

end WeilCoefficients

namespace ProEtale

variable (X : Scheme.{u})

/-- The presheaf of `ULift ℚ̄_ℓ`-algebras `U ↦ ℚ̄_ℓ,X(U)` of locally finite functions. -/
@[simps]
noncomputable def adicFunctionsAlgPresheaf :
    X.ProEtᵒᵖ ⥤ AlgCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l)) where
  obj U := AlgCat.of _ (ULift.{u + 1} (locallyFiniteFunctions l U.unop.left))
  map f := AlgCat.ofHom (uliftAlgHom (locallyFiniteFunctionsCompAlgHom l f.unop.left.base.hom))

/-- The presheaf `ℚ̄_ℓ,X` as a monoid object of the category of presheaves of `ULift ℚ̄_ℓ`-modules,
from the pointwise algebra structures. -/
noncomputable def adicFunctionsMonPresheaf :
    Mon (X.ProEtᵒᵖ ⥤ WeilCoefficients.{u} l) :=
  Monoidal.MonFunctorCategoryEquivalence.inverseObj
    (adicFunctionsAlgPresheaf l X ⋙ ModuleCat.MonModuleEquivalenceAlgebra.inverse)

/-- The underlying presheaf of the monoid `AlgebraicGeometry.ProEtale.adicFunctionsMonPresheaf`
is the underlying presheaf of `ℚ̄_ℓ,X`. -/
noncomputable def adicFunctionsMonPresheafXIso :
    (adicFunctionsMonPresheaf l X).X ≅ (adicConstantSheaf l X).obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ by ext; rfl

/-- The underlying presheaf of `ℚ̄_ℓ,X` is a presheaf of rings. -/
noncomputable instance adicConstantSheaf.monObjObj : MonObj (adicConstantSheaf l X).obj :=
  .ofIso (adicFunctionsMonPresheafXIso l X)

/-- **The constant `ℓ`-adic sheaf is a sheaf of rings**: the ring structure induced from the
pointwise multiplication of locally finite functions. -/
noncomputable instance adicConstantSheaf.monObj : MonObj (adicConstantSheaf l X) :=
  Sheaf.monObjOfPresheaf _

variable {l} in
/-- The multiplication of the underlying presheaf of `ℚ̄_ℓ,X` is the pointwise multiplication of
functions. -/
lemma adicConstantSheaf_mul_app_tmul {U : X.ProEtᵒᵖ}
    (s t : (adicConstantSheaf l X).obj.obj U) :
    (μ[(adicConstantSheaf l X).obj]).app U (s ⊗ₜ t) = ULift.up (s.down * t.down) :=
  rfl

variable {l} in
/-- The unit of the underlying presheaf of `ℚ̄_ℓ,X` is the constant function `1`. -/
lemma adicConstantSheaf_one_app {U : X.ProEtᵒᵖ} (r : ULift.{u + 1} (PadicAlgCl l)) :
    (η[(adicConstantSheaf l X).obj]).app U r = ULift.up (algebraMap _ _ r.down) :=
  rfl

section LowerStar

open Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped Obj

variable {l} {V W : Scheme.{u}} (g : W ⟶ V)

lemma adicConstantSheaf_ε_comp_map_one' (V : Scheme.{u}) :
    ε (sheafToPresheaf (Scheme.ProEt.topology V) (WeilCoefficients.{u} l)) ≫
        (sheafToPresheaf _ _).map η[adicConstantSheaf l V] =
      η[(adicConstantSheaf l V).obj] :=
  Sheaf.ε_comp_map_one _

lemma adicConstantSheaf_μ_comp_map_mul' (V : Scheme.{u}) :
    «μ» (sheafToPresheaf (Scheme.ProEt.topology V) (WeilCoefficients.{u} l)) _ _ ≫
        (sheafToPresheaf _ _).map μ[adicConstantSheaf l V] =
      μ[(adicConstantSheaf l V).obj] :=
  Sheaf.μ_comp_map_mul _

/-- **Pulling back functions is a morphism of sheaves of rings** `ℚ̄_ℓ,V ⟶ g_* ℚ̄_ℓ,W`. On the
underlying presheaves both multiplications are pointwise multiplications of functions, the
multiplication of `g_* ℚ̄_ℓ,W` restricting to that of `ℚ̄_ℓ,W` along the comparison with the
presheaf tensor product
(`CategoryTheory.Functor.μ_sheafToPresheaf_comp_map_μ_sheafPushforwardContinuous`). -/
instance isMonHom_adicConstantSheafToLowerStar :
    IsMonHom (adicConstantSheafToLowerStar l g) := by
  have : IsMonHom ((sheafToPresheaf _ _).map (adicConstantSheafToLowerStar l g)) :=
    { one_hom := by
        have h := Functor.ε_sheafToPresheaf_comp_map_ε_sheafPushforwardContinuous
          (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) (WeilCoefficients.{u} l)
          (Scheme.ProEt.topology V) (Scheme.ProEt.topology W)
        change (ε _ ≫ (sheafToPresheaf _ _).map η[adicConstantSheaf l V]) ≫ _ =
          ε _ ≫ (sheafToPresheaf _ _).map
            (ε ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).sheafPushforwardContinuous
              _ _ _) ≫
              ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).sheafPushforwardContinuous
                _ _ _).map η[adicConstantSheaf l W])
        rw [adicConstantSheaf_ε_comp_map_one', Functor.map_comp, ← Category.assoc, h,
          Category.assoc]
        rw [show (sheafToPresheaf _ _).map (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g
            ).sheafPushforwardContinuous _ _ _).map η[adicConstantSheaf l W]) =
            ((Functor.whiskeringLeft _ _ _).obj (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g
              ).op).map ((sheafToPresheaf _ _).map η[adicConstantSheaf l W]) from rfl,
          ← Functor.map_comp, adicConstantSheaf_ε_comp_map_one']
        ext U
        rfl
      mul_hom := by
        have h := Functor.μ_sheafToPresheaf_comp_map_μ_sheafPushforwardContinuous
          (A := WeilCoefficients.{u} l) (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g)
          (Scheme.ProEt.topology V) (Scheme.ProEt.topology W)
          (adicConstantSheaf l W) (adicConstantSheaf l W)
        change («μ» _ _ _ ≫ (sheafToPresheaf _ _).map μ[adicConstantSheaf l V]) ≫ _ =
          _ ≫ «μ» _ _ _ ≫ (sheafToPresheaf _ _).map
            («μ» ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).sheafPushforwardContinuous
              _ _ _) _ _ ≫
              ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).sheafPushforwardContinuous
                _ _ _).map μ[adicConstantSheaf l W])
        rw [adicConstantSheaf_μ_comp_map_mul', Functor.map_comp, reassoc_of% h]
        rw [show (sheafToPresheaf _ _).map (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g
            ).sheafPushforwardContinuous _ _ _).map μ[adicConstantSheaf l W]) =
            ((Functor.whiskeringLeft _ _ _).obj (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g
              ).op).map ((sheafToPresheaf _ _).map μ[adicConstantSheaf l W]) from rfl,
          ← Functor.map_comp, adicConstantSheaf_μ_comp_map_mul']
        refine NatTrans.ext (funext fun U ↦ ?_)
        exact ModuleCat.MonoidalCategory.tensor_ext fun s t ↦ rfl }
  exact Sheaf.isMonHom_of_isMonHom_map _

end LowerStar

end ProEtale

end AlgebraicGeometry
