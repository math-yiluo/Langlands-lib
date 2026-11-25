/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralCompactSupportDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc

/-! # Preservation on the ordinary integral localizing category -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
variable (k : Type u) [Field k]
omit [IsCommMonObj Λ] in
private theorem image_isTriangulated {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : (image Λ c).IsTriangulated := by
  change ((openImmersionLowerShriek Λ c.i).mapDerivedCategory ⋙
    (lowerStar Λ c.g).rightDerivedFunctor).IsTriangulated
  infer_instance

/-- Transport compactification preservation along the equality Dctf=Dbc. -/
private theorem preservation_of_equal_generators
    (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hcoeff : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (ht : ∀ (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S],
      localizingClosureCtfEqualsBcAssertions ℓ Λ S) : Preservation Λ k := by
  have he (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S] :
      localizingClosureProEtale Λ S = localizing Λ S :=
    (ht S).2.2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    intro X Y f c
    let : X.obj.left.Over (Spec (.of k)) := ⟨X.obj.hom⟩
    let : Y.obj.left.Over (Spec (.of k)) := ⟨Y.obj.hom⟩
    let : f.hom.left.IsOver (Spec (.of k)) := ⟨f.hom.w⟩
    let : IsSeparated X.obj.hom := X.property.1
    let : LocallyOfFiniteType X.obj.hom := X.property.2.1
    let : QuasiCompact X.obj.hom := X.property.2.2
    let : IsSeparated Y.obj.hom := Y.property.1
    let : LocallyOfFiniteType Y.obj.hom := Y.property.2.1
    let : QuasiCompact Y.obj.hom := Y.property.2.2
    let : CompactSpace X.obj.left :=
      QuasiCompact.compactSpace_of_compactSpace X.obj.hom
    let : QuasiSeparatedSpace X.obj.left :=
      quasiSeparatedSpace_of_quasiSeparated X.obj.hom
    let : CompactSpace Y.obj.left :=
      QuasiCompact.compactSpace_of_compactSpace Y.obj.hom
    let : QuasiSeparatedSpace Y.obj.left :=
      quasiSeparatedSpace_of_quasiSeparated Y.obj.hom
    have hw : f.hom.left ≫ Y.obj.hom = X.obj.hom := f.hom.w
    let : IsSeparated f.hom.left := by
      have : IsSeparated (f.hom.left ≫ Y.obj.hom) := by rw [hw]; infer_instance
      exact IsSeparated.of_comp f.hom.left Y.obj.hom
    let : LocallyOfFiniteType f.hom.left := by
      have : LocallyOfFiniteType (f.hom.left ≫ Y.obj.hom) := by rw [hw]; infer_instance
      exact locallyOfFiniteType_of_comp f.hom.left Y.obj.hom
    let : IsSeparated (X.obj.left ↘ Spec (.of k)) := X.property.1
    let : LocallyOfFiniteType (X.obj.left ↘ Spec (.of k)) := X.property.2.1
    let : QuasiCompact (X.obj.left ↘ Spec (.of k)) := X.property.2.2
    let : IsSeparated (Y.obj.left ↘ Spec (.of k)) := Y.property.1
    let : LocallyOfFiniteType (Y.obj.left ↘ Spec (.of k)) := Y.property.2.1
    let : QuasiCompact (Y.obj.left ↘ Spec (.of k)) := Y.property.2.2
    have h := compactification_localizing Λ ℓ k
      (X := X.obj.left) (Y := Y.obj.left) f.hom.left ⟨c⟩ hcoeff
  · intro K hK
    exact (congrFun (he Y.obj.left) _).mp
      (h.1 K ((congrFun (he X.obj.left) K).mpr hK))
  · intro T _ _ _ hT
    have := image_isTriangulated Λ c.obj
    exact Functor.map_distinguished (image Λ c.obj) T hT
  · intro I F hF
    exact h.2.2.1 I F (fun i ↦ (congrFun (he X.obj.left) _).mpr (hF i))
  · intro K hK
    have hctf : (constantModelBoundedConstructible Λ X.obj.left ⊓
        _root_.DerivedCategory.finiteTorAmplitude _) K :=
      (congrFun (ht X.obj.left).2.2.1 K).mpr hK
    exact (h.2.2.2 K hctf).1

/-- Source: blueprint proposition-construction-independence-rf-shriek steps 2, 3 and 6.
(blueprint: lem-sfb-total-derived-preservation).

Proof: Each standing scheme is quasi-compact and quasi-separated, since its structure
map to Spec k is quasi-compact and separated. Specialize localizingClosure_ctf_equals_bc
to O_E, using the identity coefficient-ring isomorphism. Write ht for its equality
Dctf = Dbc and he for the induced equality of their localizing closures. The coefficient
O_E is localizing-admissible by its finite-extension clause, again with the identity
isomorphism. Apply compactification_localizing to the boundary compactification c.
Transport its first, second and third clauses along he on input and output objects.
Its fourth clause preserves Dctf; ht identifies Dctf with Dbc, giving the last field.
Distinguished triangles use the existing composite shift comparison and coproducts
are the ambient discrete coproducts, including the empty diagram. -/
theorem preservation_of_ctf_eq
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    : Preservation (Profinite.padicIntegersRingObj ℓ E.val) k := by
  let O := Profinite.padicIntegersRingObj ℓ E.val
  have hcoeff : IsLocalizingAdmissibleCoefficient ℓ O :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩))))
  have ht (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S] :=
    (localizingClosure_ctf_equals_bc ℓ S O
      (Or.inr (Or.inr (Or.inl ⟨E, Or.inl ⟨Iso.refl _⟩⟩)))).1
  exact preservation_of_equal_generators O k ℓ hcoeff ht

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
