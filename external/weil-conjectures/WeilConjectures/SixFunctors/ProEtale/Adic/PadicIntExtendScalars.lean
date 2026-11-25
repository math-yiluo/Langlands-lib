/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.RingObjects.EllAdic

/-!
# Extension of scalars from `ℤ_ℓ,X`-modules to `ℚ̄_ℓ,X`-modules

On the small pro-étale site of a scheme `X`, the inclusion `ℤ_ℓ ⟶ ℚ̄_ℓ` induces a morphism of
commutative ring objects of abelian sheaves `ℤ_ℓ,X ⟶ ℚ̄_ℓ,X`
(`AlgebraicGeometry.ProEtale.padicIntSheafToPadicAlgClSheaf`), where `ℚ̄_ℓ,X` is the ring object
`AlgebraicGeometry.ProEtale.padicAlgClSheaf`, isomorphic as an abelian sheaf to the unit
`adicConstantSheaf` of the `ℓ`-adic sheaves (`padicAlgClSheafIsoAdicConstantSheaf`). Extension of
scalars along it, `M ↦ ℚ̄_ℓ,X ⊗_{ℤ_ℓ,X} M`, is left adjoint to restriction of scalars
(`AlgebraicGeometry.ProEtale.padicIntExtendRestrictAdjunction`): this is the rationalisation of
integral lattices `lim_n Fₙ` of lisse sheaves.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

/-- The inclusion `ℤ_ℓ → ℚ̄_ℓ`, as a ring homomorphism. -/
noncomputable def padicIntToPadicAlgCl : ℤ_[l] →+* PadicAlgCl l :=
  (algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom

lemma continuous_padicIntToPadicAlgCl : Continuous (padicIntToPadicAlgCl l) :=
  (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val

/-- The inclusion `ℤ_ℓ,X ⟶ ℚ̄_ℓ,X` of commutative ring objects of abelian sheaves on `X_proét`. -/
noncomputable def padicIntSheafToPadicAlgClSheaf :
    (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (padicIntSheaf X l) ⟶ padicAlgClSheaf X l :=
  continuousMapRingSheafToPadicAlgClSheaf X l (padicIntToPadicAlgCl l)
    (continuous_padicIntToPadicAlgCl l)
    ⟨⊥, inferInstance, fun t ↦ IntermediateField.algebraMap_mem ⊥ (t : ℚ_[l])⟩

instance : IsMonHom (padicIntSheafToPadicAlgClSheaf X l) := by
  unfold padicIntSheafToPadicAlgClSheaf
  infer_instance

/-- Extension of scalars `M ↦ ℚ̄_ℓ,X ⊗_{ℤ_ℓ,X} M` from module objects over `ℤ_ℓ,X` to module
objects over `ℚ̄_ℓ,X` in abelian sheaves on `X_proét`. -/
noncomputable abbrev padicIntExtendScalars :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        ((sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (padicIntSheaf X l)) ⥤
      Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClSheaf X l) :=
  Mod.extendScalars (padicIntSheafToPadicAlgClSheaf X l)

/-- Extension of scalars from `ℤ_ℓ,X`-modules to `ℚ̄_ℓ,X`-modules is left adjoint to restriction
of scalars along `ℤ_ℓ,X ⟶ ℚ̄_ℓ,X`. -/
noncomputable def padicIntExtendRestrictAdjunction :
    padicIntExtendScalars X l ⊣ Mod.comap (padicIntSheafToPadicAlgClSheaf X l) :=
  Mod.extendRestrictAdjunction _

end AlgebraicGeometry.ProEtale
