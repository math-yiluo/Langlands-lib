/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NoetherianLocalModelTower
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.AlgebraicGeometry.LimitTowerEssentiallyFinitePresentation
import WeilConjectures.RingTheory.NoetherianLocalModelTowerOfCategoricalLimit
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Localization.Basic

/-!
# Construction of a Noetherian local model tower

Source: Stacks Project, Algebra, proof of Tag 00R7, first paragraph and the
transition-localization sentence in its second paragraph.
(blueprint: lem-weil-pbc-noetherian-local-model-tower-existence).
-/

@[expose] public section

universe u v w t p q

namespace Module

/-- An essentially finitely presented local tower and a finitely presented module admit
Noetherian local models, with transition and limit localization comparisons.
Source: Stacks Project, Algebra, proof of Tag 00R7, first paragraph and the
transition-localization sentence in the second paragraph.
(blueprint: lem-weil-pbc-noetherian-local-model-tower-existence).

Proof:
1. Lift the three rings to `Type (max u v w)` by `ULift`, transporting their ring,
   algebra and local structures along the canonical ring equivalences. Transport the
   localized presentations over `P` and `Q` by composition with these equivalences.
   The module remains in `Type t`, with the transported top-ring action. A finite
   presentation supplies a finite matrix whose cokernel is the module.
2. Apply `RingHom.limit_tower_essentially_finite_presentation` to the lifted
   tower and this matrix. Its rings are essentially of finite type successively over
   the integers, hence Noetherian: finite type algebras over Noetherian rings are
   Noetherian, as are their localizations. Restrict stage-module actions along the two
   stage ring maps; all stage scalar towers then follow from composition.
3. Use the functors' maps for the transitions, the specified colimit cocones for the
   maps to the limit, and transport the latter through `ULift.down`. The elementwise
   characterization of a filtered colimit supplies the four representation and eventual
   equality clauses. Naturality supplies all commutative squares and semilinearity.
4. Compose the middle- and top-ring transition localizations: tensor associativity,
   localization base change and localization of a localization show that
   `Tᵢ ⊗[Rᵢ] Rⱼ → Tⱼ` is a localization. The other transition clauses come directly
   from the tower theorem.
5. Tensor symmetry converts the limit middle-ring localization to
   `R ⊗[Rᵢ] Sᵢ`. A ring localization is its module localization. For the module put
   `C = S ⊗[Sᵢ] Tᵢ`, acting canonically on `S ⊗[Sᵢ] Nᵢ`. The top-ring limit clause
   identifies `S'` with a localization of `C`; its module clause identifies `M` with
   `S' ⊗[Tᵢ] Nᵢ`. Tensor associativity and localization-tensor compatibility identify
   this with the localization of `S ⊗[Sᵢ] Nᵢ` at the same submonoid, `S`-linearly.
   Transport these comparisons through the lift equivalences. No flatness was used.
-/
theorem exists_noetherian_localModelTower
    (R : Type u) (S : Type v) (S' : Type w) (M : Type t)
    [CommRing R] [CommRing S] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
    [AddCommGroup M] [Module S' M] [Module S M] [Module R M]
    [IsScalarTower S S' M] [IsScalarTower R S M]
    (P : Type p) (Q : Type q) [CommRing P] [CommRing Q]
    [Algebra R P] [Algebra P S] [IsScalarTower R P S]
    [Algebra R Q] [Algebra Q S'] [IsScalarTower R Q S']
    [Algebra.FinitePresentation R P] [Algebra.FinitePresentation R Q]
    (W : Submonoid P) (V : Submonoid Q) [IsLocalization W S] [IsLocalization V S']
    [Module.FinitePresentation S' M] :
    Nonempty (NoetherianLocalModelTower R S S' M) := by
  classical
  let R₁ := ULift.{max u v w} R
  let S₁ := ULift.{max u v w} S
  let T₁ := ULift.{max u v w} S'
  let α : R₁ →+* S₁ := (algebraMap R S).ulift
  let β : S₁ →+* T₁ := (algebraMap S S').ulift
  have : IsLocalHom (ULift.ringEquiv : R₁ ≃+* R).toRingHom :=
    ⟨fun a h ↦ h.map (ULift.ringEquiv : R₁ ≃+* R).symm.toRingHom⟩
  have : IsLocalHom (ULift.ringEquiv : S₁ ≃+* S).toRingHom :=
    ⟨fun a h ↦ h.map (ULift.ringEquiv : S₁ ≃+* S).symm.toRingHom⟩
  have : IsLocalHom (ULift.ringEquiv : T₁ ≃+* S').toRingHom :=
    ⟨fun a h ↦ h.map (ULift.ringEquiv : T₁ ≃+* S').symm.toRingHom⟩
  have : IsLocalRing R₁ := RingHom.domain_isLocalRing ULift.ringEquiv.toRingHom
  have : IsLocalRing S₁ := RingHom.domain_isLocalRing ULift.ringEquiv.toRingHom
  have : IsLocalRing T₁ := RingHom.domain_isLocalRing ULift.ringEquiv.toRingHom
  have : IsLocalHom α := by dsimp [α, RingHom.ulift]; infer_instance
  have : IsLocalHom β := by dsimp [β, RingHom.ulift]; infer_instance
  let : Algebra R₁ P := ULift.algebra' R P
  let : Algebra R₁ Q := ULift.algebra' R Q
  have : Algebra.FinitePresentation R₁ P := by
    apply RingHom.finitePresentation_algebraMap.mp
    exact (RingHom.finitePresentation_algebraMap.mpr
      (inferInstance : Algebra.FinitePresentation R P)).comp
        (RingHom.FinitePresentation.of_bijective
          (show Function.Bijective (ULift.ringEquiv : R₁ ≃+* R).toRingHom from
            ULift.ringEquiv.bijective))
  have : Algebra.FinitePresentation R₁ Q := by
    apply RingHom.finitePresentation_algebraMap.mp
    exact (RingHom.finitePresentation_algebraMap.mpr
      (inferInstance : Algebra.FinitePresentation R Q)).comp
        (RingHom.FinitePresentation.of_bijective
          (show Function.Bijective (ULift.ringEquiv : R₁ ≃+* R).toRingHom from
            ULift.ringEquiv.bijective))
  let f : P →+* S₁ := ULift.ringEquiv.symm.toRingHom.comp (algebraMap P S)
  let g : Q →+* T₁ := ULift.ringEquiv.symm.toRingHom.comp (algebraMap Q S')
  have hf : f.comp (algebraMap R₁ P) = α := by
    ext x
    exact (IsScalarTower.algebraMap_apply R P S x.down).symm
  have hg : g.comp (algebraMap R₁ Q) = β.comp α := by
    ext x
    exact (IsScalarTower.algebraMap_apply R Q S' x.down).symm.trans
      (IsScalarTower.algebraMap_apply R S S' x.down)
  have hS : letI := f.toAlgebra; IsLocalization W S₁ :=
    (IsLocalization.isLocalization_iff_of_ringEquiv W
      (ULift.ringEquiv : S₁ ≃+* S).symm).mp inferInstance
  have hT : letI := g.toAlgebra; IsLocalization V T₁ :=
    (IsLocalization.isLocalization_iff_of_ringEquiv V
      (ULift.ringEquiv : T₁ ≃+* S').symm).mp inferInstance
  let : Algebra T₁ S' := ULift.algebra' S' S'
  have : Module.FinitePresentation T₁ S' := by
    let e : T₁ ≃ₗ[T₁] S' :=
      { ULift.ringEquiv.toAddEquiv with map_smul' := fun _ _ ↦ rfl }
    exact Module.FinitePresentation.of_equiv e
  have : Module.FinitePresentation T₁ M := Module.FinitePresentation.trans T₁ M S'
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin T₁ M
  obtain ⟨m, H, hH⟩ := K.fg_iff_exists_fin_linearMap.mp hK
  have hM : Nonempty (((Fin n → T₁) ⧸ LinearMap.range H) ≃ₗ[T₁] M) := by
    rw [hH]
    exact ⟨e.symm⟩
  have hlimit := RingHom.limit_tower_essentially_finite_presentation
    α β P W f hf hS Q V g hg hT M m n H hM
  exact noetherian_localModelTower_of_categoricalLimit R S S' M m n hlimit

end Module
