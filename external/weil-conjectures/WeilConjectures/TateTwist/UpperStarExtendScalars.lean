/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.MapIsoUnit
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.TateTwist.ProEtale

/-!
# Extension of scalars of a locally trivial module

Let `g : U ⟶ X` be a morphism of schemes and `a : Λ ⟶ Λ'` a morphism of commutative condensed
rings. If the pullback along `g` of a `Λ_X`-module `T` is trivial, then so is the pullback of its
extension of scalars `Λ'_X ⊗_{Λ_X} T`
(`AlgebraicGeometry.ProEtale.upperStarMapModExtendScalarsIsoUnit`). This applies to the Tate
module `ℤ_ℓ(1)` and the Tate twist `ℚ̄_ℓ(1) = ℚ̄_ℓ ⊗_{ℤ_ℓ} ℤ_ℓ(1)`: the pullback of module
objects commutes with extension of scalars (`ProEtale.CondensedRing.pullIso`), and extension of
scalars is strong monoidal, so it sends the unit to the unit.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X U : Scheme.{u}} (g : U ⟶ X)
  {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

/-- If the pullback of a `Λ_X`-module `T` along `g` is trivial, so is the pullback of its extension
of scalars `Λ'_X ⊗_{Λ_X} T`, as a module over `Λ'_U`. -/
noncomputable def upperStarExtendScalarsIsoUnit (T : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))
    (e : ((g)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)).obj T ≅ 𝟙_ _) :
    (CondensedRing.upperStar Λ' g).obj ((Mod.extendScalars (coefficientMap a X)).obj T) ≅
      𝟙_ _ :=
  letI := Mod.extendScalarsMonoidal (condensedPullbackHom Λ g)
  letI := Mod.extendScalarsMonoidal (coefficientMap a U)
  ((CondensedRing.pullIso a g).app T).symm ≪≫
    (Mod.extendScalars (coefficientMap a U)).mapIso
      ((Mod.extendScalars (condensedPullbackHom Λ g)).mapIso e ≪≫ Functor.mapUnitIsoUnit _) ≪≫
    Functor.mapUnitIsoUnit _

/-- If the pullback of a `Λ_X`-module `T` along `g` is trivial, so is the pullback of its extension
of scalars `Λ'_X ⊗_{Λ_X} T`, as a module over `g^* Λ'_X`. -/
noncomputable def upperStarMapModExtendScalarsIsoUnit
    (T : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (e : ((g)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)).obj T ≅ 𝟙_ _) :
    ((g)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ' X)).obj
      ((Mod.extendScalars (coefficientMap a X)).obj T) ≅ 𝟙_ _ :=
  letI := Mod.extendScalarsMonoidal (condensedPullbackHom Λ' g)
  (Mod.extendScalars (condensedPullbackHom Λ' g)).preimageIso
    (upperStarExtendScalarsIsoUnit g a T e ≪≫ (Functor.mapUnitIsoUnit _).symm)

end AlgebraicGeometry.ProEtale
