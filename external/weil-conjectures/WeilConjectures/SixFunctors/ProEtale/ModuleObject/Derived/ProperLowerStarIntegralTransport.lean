/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapRingObjMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionOpenLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!
# Transport of `Rp_*` on `Dᵇc(-)⟦𝒪̲_E⟧` along isomorphisms of the coefficient field

Let `E₁, E₂` be finite extensions of `ℚ_ℓ` embedded in `ℚ̄_ℓ`, and `σ : E₁ ≃+* E₂` a field
isomorphism compatible with the embeddings. Then `σ` restricts to an isometric isomorphism
`𝒪_{E₁} ≃+* 𝒪_{E₂}` (`PadicAlgCl.integersRingEquivOfComp`), hence induces an isomorphism of
condensed coefficient rings `𝒪̲_{E₁} ≅ 𝒪̲_{E₂}` (`Profinite.padicIntegersRingObjMapOfRingEquiv`).
The restriction of scalars along it is an equivalence of the bounded constructible derived
categories (`ProEtale.CondensedRing.boundedConstructibleComapEquivalence`) commuting with the
derived pushforward (`ProEtale.CondensedRing.rightDerivedLowerStarComapIso`). Hence
`Rp_* : Dᵇc(Z)⟦𝒪̲_{E₁}⟧ ⥤ Dᵇc(Y)⟦𝒪̲_{E₁}⟧` is a left adjoint as soon as the one for `E₂` is
(`isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj_of_ringEquiv`).

Applied to the image of an embedded field `E ⟶ ℚ̄_ℓ`, a finite intermediate field of `ℚ̄_ℓ / ℚ_ℓ`,
this reduces the left adjointness of `Rp_*` for an arbitrary embedded `E` to the case of
`PadicAlgCl.FiniteIntermediateField`
(`isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj_of_finiteIntermediateField`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

/-! ### The isomorphism of rings of integers -/

namespace PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] {E₁ E₂ : Type} [Field E₁] [Algebra E₁ (PadicAlgCl ℓ)] [Field E₂]
  [Algebra E₂ (PadicAlgCl ℓ)] (σ : E₁ ≃+* E₂)
  (hσ : ∀ x, algebraMap E₂ (PadicAlgCl ℓ) (σ x) = algebraMap E₁ (PadicAlgCl ℓ) x)

/-- A field isomorphism `σ : E₁ ≃+* E₂` compatible with the embeddings into `ℚ̄_ℓ` restricts to
an isomorphism `𝒪_{E₁} ≃+* 𝒪_{E₂}` of the rings of integers. -/
noncomputable def integersRingEquivOfComp : integers ℓ E₁ ≃+* integers ℓ E₂ where
  toFun x := ⟨σ x, (mem_integers_iff ℓ E₂ _).2 (by rw [hσ]; exact x.2)⟩
  invFun y := ⟨σ.symm y, (mem_integers_iff ℓ E₁ _).2 (by rw [← hσ, σ.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x)
  right_inv y := Subtype.ext (σ.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul σ (x : E₁) y)
  map_add' x y := Subtype.ext (map_add σ (x : E₁) y)

/-- The inverse `σ.symm` of a field isomorphism compatible with the embeddings into `ℚ̄_ℓ` is
compatible with them. -/
lemma symm_comp_apply_eq
    (hσ : ∀ x, algebraMap E₂ (PadicAlgCl ℓ) (σ x) = algebraMap E₁ (PadicAlgCl ℓ) x) (y : E₂) :
    algebraMap E₁ (PadicAlgCl ℓ) (σ.symm y) = algebraMap E₂ (PadicAlgCl ℓ) y := by
  rw [← hσ, σ.apply_symm_apply]

/-- The isomorphism `𝒪_{E₁} ≃+* 𝒪_{E₂}` induced by `σ` is continuous, `σ` being an isometry for
the norms restricted from `ℚ̄_ℓ`. -/
lemma continuous_integersRingEquivOfComp :
    letI := normedFieldOfAlgebra ℓ E₁
    letI := normedFieldOfAlgebra ℓ E₂
    Continuous (integersRingEquivOfComp σ hσ) := by
  let _ := normedFieldOfAlgebra ℓ E₁
  let _ := normedFieldOfAlgebra ℓ E₂
  have hiso : Isometry σ := AddMonoidHomClass.isometry_of_norm σ fun x ↦
    (congrArg norm (hσ x) :
      ‖algebraMap E₂ (PadicAlgCl ℓ) (σ x)‖ = ‖algebraMap E₁ (PadicAlgCl ℓ) x‖)
  exact (hiso.continuous.comp continuous_subtype_val).subtype_mk _

end PadicAlgCl

/-! ### The isomorphism of condensed rings of integers -/

namespace Profinite

variable (ℓ : ℕ) [Fact ℓ.Prime] {E₁ E₂ : Type} [Field E₁] [Algebra E₁ (PadicAlgCl ℓ)] [Field E₂]
  [Algebra E₂ (PadicAlgCl ℓ)] (σ : E₁ ≃+* E₂)
  (hσ : ∀ x, algebraMap E₂ (PadicAlgCl ℓ) (σ x) = algebraMap E₁ (PadicAlgCl ℓ) x)

/-- The morphism of condensed rings `𝒪̲_{E₁} ⟶ 𝒪̲_{E₂}` induced by a field isomorphism
`σ : E₁ ≃+* E₂` compatible with the embeddings into `ℚ̄_ℓ`. -/
noncomputable def padicIntegersRingObjMapOfRingEquiv :
    padicIntegersRingObj.{u} ℓ E₁ ⟶ padicIntegersRingObj ℓ E₂ :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E₁
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E₂
  continuousMapRingObjMap (PadicAlgCl.integersRingEquivOfComp σ hσ).toRingHom
    (PadicAlgCl.continuous_integersRingEquivOfComp σ hσ)

instance : IsMonHom (padicIntegersRingObjMapOfRingEquiv.{u} ℓ σ hσ) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E₁
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E₂
  inferInstanceAs (IsMonHom (continuousMapRingObjMap.{u}
    (PadicAlgCl.integersRingEquivOfComp σ hσ).toRingHom
    (PadicAlgCl.continuous_integersRingEquivOfComp σ hσ)))

/-- Composing the morphisms induced by `σ` and `σ.symm` gives the identity. -/
lemma padicIntegersRingObjMapOfRingEquiv_comp_symm :
    padicIntegersRingObjMapOfRingEquiv.{u} ℓ σ hσ ≫
      padicIntegersRingObjMapOfRingEquiv ℓ σ.symm (PadicAlgCl.symm_comp_apply_eq σ hσ) = 𝟙 _ := by
  let _ := PadicAlgCl.normedFieldOfAlgebra ℓ E₁
  let _ := PadicAlgCl.normedFieldOfAlgebra ℓ E₂
  refine (continuousMapRingObjMap_comp _ _ _ _).symm.trans (continuousMapRingObjMap_eq_id _ _ ?_)
  ext x
  exact σ.symm_apply_apply x

instance : IsIso (padicIntegersRingObjMapOfRingEquiv.{u} ℓ σ hσ) :=
  ⟨padicIntegersRingObjMapOfRingEquiv ℓ σ.symm (PadicAlgCl.symm_comp_apply_eq σ hσ),
    padicIntegersRingObjMapOfRingEquiv_comp_symm ℓ σ hσ,
    padicIntegersRingObjMapOfRingEquiv_comp_symm ℓ σ.symm _⟩

end Profinite

/-! ### Restriction of scalars along an isomorphism of coefficient rings -/

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

open scoped CategoryTheory.Functor

section Comap

variable {X : Scheme.{u}} {R T : Sheaf (ProEt.topology X) Ab.{u + 1}} [MonObj R] [MonObj T]
  [IsCommMonObj R] [IsCommMonObj T] (φ : R ⟶ T) [IsMonHom φ] [IsIso φ]

omit [IsCommMonObj R] [IsCommMonObj T] in
/-- The restriction of scalars along an isomorphism `φ : R ⟶ T` of ring objects on `X_proét`
preserves bounded constructible complexes: it is exact, hence preserves boundedness and commutes
with the cohomology sheaves, and it preserves constructible module objects. -/
lemma boundedConstructible_mapDerivedCategory_comap_obj
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) T)}
    (hK : boundedConstructible T K) : boundedConstructible R (D(Mod.comap φ).obj K) :=
  ⟨Functor.bounded_mapDerivedCategory_obj _ hK.1, fun i ↦
    IsConstructibleModuleObject.of_iso
      (((Mod.comap φ).mapDerivedCategoryHomologyFunctorIso i).app K)
      (constructible_comap φ (hK.2 i))⟩

/-- The restriction of scalars along an isomorphism `φ : R ⟶ T` of ring objects on `X_proét`,
as an equivalence of derived categories `D(X, T) ≌ D(X, R)`. -/
noncomputable def comapDerivedEquivalence :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) T) ≌
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) :=
  have : (Mod.comapEquivalenceOfIsIso φ).functor.Additive :=
    inferInstanceAs (Mod.comap φ).Additive
  have : (Mod.comapEquivalenceOfIsIso φ).inverse.Additive :=
    inferInstanceAs (Mod.comap (asIso φ).inv).Additive
  (Mod.comapEquivalenceOfIsIso φ).mapDerivedCategory

/-- The restriction of scalars along an isomorphism `φ : R ⟶ T` of ring objects on `X_proét`,
as an equivalence of bounded constructible derived categories `Dᵇc(X, T) ≌ Dᵇc(X, R)`. -/
noncomputable def boundedConstructibleComapEquivalence :
    (boundedConstructible T).FullSubcategory ≌ (boundedConstructible R).FullSubcategory :=
  (comapDerivedEquivalence φ).congrFullSubcategory <| by
    ext K
    refine ⟨fun hK ↦ ?_, boundedConstructible_mapDerivedCategory_comap_obj φ⟩
    exact (boundedConstructible T).prop_of_iso ((comapDerivedEquivalence φ).unitIso.app K).symm
      (boundedConstructible_mapDerivedCategory_comap_obj (asIso φ).inv hK)

end Comap

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {E₁ E₂ : Type} [Field E₁] [Algebra E₁ (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E₁]
  [IsScalarTower ℚ_[ℓ] E₁ (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E₁] [Field E₂]
  [Algebra E₂ (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E₂] [IsScalarTower ℚ_[ℓ] E₂ (PadicAlgCl ℓ)]
  [FiniteDimensional ℚ_[ℓ] E₂]
  {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **Transport of the left adjointness of `Rp_*` along an isomorphism of coefficient fields**:
if `σ : E₁ ≃+* E₂` is compatible with the embeddings into `ℚ̄_ℓ` and
`Rp_* : Dᵇc(Z)⟦𝒪̲_{E₂}⟧ ⥤ Dᵇc(Y)⟦𝒪̲_{E₂}⟧` is a left adjoint, then so is
`Rp_* : Dᵇc(Z)⟦𝒪̲_{E₁}⟧ ⥤ Dᵇc(Y)⟦𝒪̲_{E₁}⟧`. The restriction of scalars along the induced
isomorphism `𝒪̲_{E₁} ≅ 𝒪̲_{E₂}` is an equivalence of the bounded constructible derived categories
(`boundedConstructibleComapEquivalence`) commuting with `Rp_*`
(`rightDerivedLowerStarComapIso`), so the two `Rp_*` are conjugate. -/
theorem isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj_of_ringEquiv
    (σ : E₁ ≃+* E₂)
    (hσ : ∀ x, algebraMap E₂ (PadicAlgCl ℓ) (σ x) = algebraMap E₁ (PadicAlgCl ℓ) x)
    (p : Z ⟶ Y) (h : (PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E₂ p).IsLeftAdjoint) :
    (PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E₁ p).IsLeftAdjoint := by
  let a := Profinite.padicIntegersRingObjMapOfRingEquiv.{u} ℓ σ hσ
  let eZ := boundedConstructibleComapEquivalence (coefficientMap a Z.left)
  let eY := boundedConstructibleComapEquivalence (coefficientMap a Y.left)
  let iso : PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E₂ p ⋙ eY.functor ≅
      eZ.functor ⋙ PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E₁ p :=
    ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
      (Functor.isoWhiskerLeft (boundedConstructible _).ι (rightDerivedLowerStarComapIso a p.left))
  exact Functor.isLeftAdjoint_of_iso ((Functor.isoWhiskerLeft eZ.inverse iso.symm).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eZ.counitIso _ ≪≫
    Functor.leftUnitor _)

/-- **Reduction to finite intermediate fields**: if
`Rp_* : Dᵇc(Z)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y)⟦𝒪̲_E⟧` is a left adjoint for every finite subextension `E ⊆ ℚ̄_ℓ`
of `ℚ_ℓ`, then it is a left adjoint for every finite extension `E` of `ℚ_ℓ` embedded in `ℚ̄_ℓ`:
`E` is isomorphic, compatibly with the embeddings, to its image in `ℚ̄_ℓ`. -/
theorem isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj_of_finiteIntermediateField
    (p : Z ⟶ Y)
    (h : ∀ E' : PadicAlgCl.FiniteIntermediateField ℓ,
      (PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E'.1 p).IsLeftAdjoint)
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    (PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E p).IsLeftAdjoint := by
  let f := IsScalarTower.toAlgHom ℚ_[ℓ] E (PadicAlgCl ℓ)
  let E' : PadicAlgCl.FiniteIntermediateField ℓ :=
    ⟨f.fieldRange, (AlgEquiv.ofInjectiveField f).toLinearEquiv.finiteDimensional⟩
  have : FiniteDimensional ℚ_[ℓ] E'.1 := E'.2
  exact isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj_of_ringEquiv ℓ
    (E₂ := E'.1) (AlgEquiv.ofInjectiveField f).toRingEquiv (fun _ ↦ rfl) p (h E')

end AlgebraicGeometry.ProEtale.CondensedRing
