/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.NatTransId
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Linear
public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.CoefficientLinear
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar

/-!
# Scalar multiplication by a finite subextension on `F_X`-modules

Let `Λ` be a commutative condensed ring and `φ : K →+* Γ Λ` a ring homomorphism to its global
sections. The constant global sections `p_X^* (φ a)` of `Λ_X = p_X^* Λ` make the category of
`Λ_X`-module objects `K`-linear (`ProEtale.CondensedRing.modLinear`), and the derived pushforward
`Rf_*` is `K`-linear (`ProEtale.CondensedRing.linear_rightDerivedLowerStar`); see
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.CoefficientLinear`. So is its restriction
`Rg_*` to bounded constructible complexes
(`ProEtale.CondensedRing.linear_boundedConstructibleLowerStar`).

For a finite subextension `F ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and `Λ = F̲`, the constant global sections
`F →+* Γ F̲` give the `F`-linear structure on `F_X`-module objects
(`ProEtale.CondensedRing.padicSubfieldModLinear`, a scoped instance), hence on their derived
category and on `Dᵇc(X)⟦F̲⟧`: the scalar `b ∈ F` acts on every object by a natural endomorphism
of the identity functor, and `Rg_*` commutes with it
(`ProEtale.CondensedRing.boundedConstructibleLowerStar_map_smul_id`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

/-! ### Finite subextensions `F ⊆ ℚ̄_ℓ` -/

section Subfield

variable (ℓ : ℕ) [Fact ℓ.Prime] (F : FiniteIntermediateField ℓ)

/-- The constant global sections `F →+* Γ(F_X)` of the coefficient ring `F_X = p_X^* F̲`. -/
noncomputable def padicSubfieldConstRingHom (X : Scheme.{u}) :
    F →+* Γ (padicSubfieldRingObj X ℓ F) :=
  constRingHom _ (Profinite.continuousMapConstRingHom.{u} F) X

/-- The `F`-linear structure on `F_X`-module objects: `b : F` acts by multiplication by the
constant global section `b` of `F_X`. -/
@[instance_reducible]
noncomputable def padicSubfieldModLinear (X : Scheme.{u}) :
    Linear F (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) :=
  modLinear _ (Profinite.continuousMapConstRingHom.{u} F) X

attribute [scoped instance] padicSubfieldModLinear

/-- The action of `b ∈ F` on a morphism of `F_X`-module objects is the composition with the
multiplication by the constant global section `b`. -/
lemma padicSubfield_smul_hom (X : Scheme.{u}) (b : F)
    {M N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)} (f : M ⟶ N) :
    (b • f).hom = f.hom ≫ Mod.globalSmul (padicSubfieldConstRingHom ℓ F X b).hom N :=
  Mod.linearOfRingHom_smul_hom _ b f

/-- On the derived category of `F_X`-module objects, the action of `b ∈ F` on (the image of) a
complex `M` is the image of the multiplication by the constant global section `b` in each
degree. -/
lemma padicSubfield_smul_id_Q_obj {X : Scheme.{u}}
    (M : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ F)) ℤ) (b : F) :
    b • 𝟙 (DerivedCategory.Q.obj M) = DerivedCategory.Q.map
      ((HomologicalComplex.natTransId (Mod.smulNatTrans (padicSubfieldConstRingHom ℓ F X b).hom)
        (ComplexShape.up ℤ)).app M) :=
  smul_id_Q_obj _ (Profinite.continuousMapConstRingHom.{u} F) M b

variable {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (g : Z ⟶ Y)

/-- The derived pushforward `Rg_* : Dᵇc(Z)⟦F̲⟧ ⥤ Dᵇc(Y)⟦F̲⟧` on bounded constructible complexes
is `K`-linear, for any ring homomorphism `φ : K →+* Γ F̲`. -/
lemma linear_boundedConstructibleLowerStar {K : Type*} [Ring K]
    (φ : K →+* Γ (Profinite.continuousMapRingObj.{u} F)) :
    letI := modLinear _ φ Z.left
    letI := modLinear _ φ Y.left
    (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ F g).Linear K :=
  letI := modLinear _ φ Z.left
  letI := modLinear _ φ Y.left
  haveI := linear_rightDerivedLowerStar _ φ g.left
  ObjectProperty.lift_linear K _ _ _

/-- The pushforward `g_*` of `F_X`-module objects is `F`-linear. -/
instance linear_lowerStar_padicSubfield :
    ((g.left)_*⟦Profinite.continuousMapRingObj F⟧).Linear F :=
  linear_lowerStar _ (Profinite.continuousMapConstRingHom.{u} F) g.left

/-- The derived pushforward `Rg_*` of `F_X`-module objects is `F`-linear. -/
instance linear_rightDerivedLowerStar_padicSubfield :
    (R((g.left)_*⟦Profinite.continuousMapRingObj F⟧)).Linear F :=
  linear_rightDerivedLowerStar _ (Profinite.continuousMapConstRingHom.{u} F) g.left

/-- The derived pushforward `Rg_* : Dᵇc(Z)⟦F⟧ ⥤ Dᵇc(Y)⟦F⟧` on bounded constructible complexes is
`F`-linear. -/
instance linear_boundedConstructibleLowerStar_padicSubfield :
    (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ F g).Linear F :=
  linear_boundedConstructibleLowerStar ℓ F g (Profinite.continuousMapConstRingHom.{u} F)

/-- The derived pushforward `Rg_*` on bounded constructible complexes commutes with the
multiplication by a scalar `b ∈ F`. -/
lemma boundedConstructibleLowerStar_map_smul_id (b : F)
    (K : Dᵇc(Z.left)⟦Profinite.continuousMapRingObj F⟧) :
    (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ F g).map (b • 𝟙 K) =
      b • 𝟙 _ :=
  ((ContinuousMapRingObj.boundedConstructibleLowerStar ℓ F g).map_smul b (𝟙 K)).trans
    (congrArg (b • ·) ((ContinuousMapRingObj.boundedConstructibleLowerStar ℓ F g).map_id K))

end Subfield

end AlgebraicGeometry.ProEtale.CondensedRing
