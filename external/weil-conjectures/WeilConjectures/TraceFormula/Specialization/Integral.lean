/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.CompactSupportExchange
public import WeilConjectures.TraceFormula.Specialization.SupportExchange

/-!

# The integral of a specialized section

Let `T` be specialization data from a correspondence `c` over `k` with fixed locus `F` to a
correspondence `c'` over `k'` with fixed locus `F'` (`TraceSpecialization`), whose dualizing map
`θ_F` is the dualizing map of a compact-support exchange `ν_F : Ra_{F'!} Ψ_F ⟶ Ψ_s Ra_{F!}` of
the structure maps (`ProEtale.CondensedRing.dualizingExchange`). If `F'` is proper, the integral of
the specialization `sp_F(z) = θ_F Ψ_F(z) σ_F` of a Borel–Moore section `z` is
```
∫_{F'} sp_F(z) = σ_s⁻¹ ∘ Ψ_s(z^♭) ∘ S,     S = ν_F(ℚ̄_ℓ) ∘ Ra_{F'!}(σ_F) ∘ [F'],
```
where `z^♭ : Ra_{F!} ℚ̄_ℓ ⟶ ℚ̄_ℓ` is the adjoint of `z` and `[F'] : ℚ̄_ℓ ⟶ Ra_{F'!} ℚ̄_ℓ` the unit
class of the proper scheme `F'`
(`ProEtale.CondensedRing.Correspondence.TraceSpecialization.integral_sp_eq`). The morphism `S`
does not depend on `z`: it is the specialization of the unit class of `F`.

For the specialization data determined by the support
(`ProEtale.CondensedRing.Correspondence.TraceSpecialization.ofSupportExchange`), whose exceptional
exchange `β_c` and dualizing map `θ_X` come from compact-support exchanges `ν_c`, `ν_X`, the
dualizing map `θ_F` is the dualizing map of the composite of `ν_X` with the compact-support exchange
`ν_d` whose mate is `β_d`
(`ProEtale.CondensedRing.Correspondence.TraceSpecialization.θF_ofSupportExchange`;

blueprint `lemma-compatibilities-base-change-maps` (3)).

## Main definitions

- `ProEtale.CondensedRing.BorelMooreSection.unitClass`: the unit class `ℚ̄_ℓ ⟶ Ra_! ℚ̄_ℓ` of a
  proper scheme.
- `ProEtale.CondensedRing.compExchange`: the composite of two exchange transformations through
  composition isomorphisms.

## Main statements

- `ProEtale.CondensedRing.Correspondence.TraceSpecialization.integral_sp_eq`: the integral of a
  specialized section.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Abstract

variable {𝒜 𝒜' ℬ ℬ' 𝒮 𝒮' : Type*} [Category 𝒜] [Category 𝒜'] [Category ℬ] [Category ℬ']
  [Category 𝒮] [Category 𝒮']

/-- The composite `K(e⁻¹) ∘ ν_a(d) ∘ a'(ν_d) ∘ e'` of two exchange transformations
`ν_d : G ⋙ d' ⟶ d ⋙ H` and `ν_a : H ⋙ a' ⟶ a ⋙ K`, read through isomorphisms `e : f ≅ d ⋙ a`
and `e' : f' ≅ d' ⋙ a'`. -/
@[simps]
def compExchange {G : 𝒜 ⥤ 𝒜'} {H : ℬ ⥤ ℬ'} {K : 𝒮 ⥤ 𝒮'} {d : 𝒜 ⥤ ℬ} {d' : 𝒜' ⥤ ℬ'}
    {a : ℬ ⥤ 𝒮} {a' : ℬ' ⥤ 𝒮'} {f : 𝒜 ⥤ 𝒮} {f' : 𝒜' ⥤ 𝒮'} (e : f ≅ d ⋙ a) (e' : f' ≅ d' ⋙ a')
    (νd : G ⋙ d' ⟶ d ⋙ H) (νa : H ⋙ a' ⟶ a ⋙ K) : G ⋙ f' ⟶ f ⋙ K where
  app M := e'.hom.app (G.obj M) ≫ a'.map (νd.app M) ≫ νa.app (d.obj M) ≫ K.map (e.inv.app M)
  naturality M N g := by
    have h₁ := e'.hom.naturality (G.map g)
    have h₂ := νd.naturality g
    have h₃ := νa.naturality (d.map g)
    have h₄ := e.inv.naturality g
    simp only [Functor.comp_obj, Functor.comp_map] at h₁ h₂ h₃ h₄ ⊢
    rw [reassoc_of% h₁, ← a'.map_comp_assoc, h₂, a'.map_comp_assoc, reassoc_of% h₃,
      ← K.map_comp, h₄, K.map_comp]
    simp only [Category.assoc]

lemma compExchange_app_comp {G : 𝒜 ⥤ 𝒜'} {H : ℬ ⥤ ℬ'} {K : 𝒮 ⥤ 𝒮'} {d : 𝒜 ⥤ ℬ}
    {d' : 𝒜' ⥤ ℬ'} {a : ℬ ⥤ 𝒮} {a' : ℬ' ⥤ 𝒮'} {f : 𝒜 ⥤ 𝒮} {f' : 𝒜' ⥤ 𝒮'} (e : f ≅ d ⋙ a)
    (e' : f' ≅ d' ⋙ a') (νd : G ⋙ d' ⟶ d ⋙ H) (νa : H ⋙ a' ⟶ a ⋙ K) (M : 𝒜) :
    (compExchange e e' νd νa).app M ≫ K.map (e.hom.app M) =
      e'.hom.app (G.obj M) ≫ a'.map (νd.app M) ≫ νa.app (d.obj M) := by
  simp [compExchange, ← K.map_comp]

variable {L : 𝒜 ⥤ 𝒮} {R : 𝒮 ⥤ 𝒜} {L' : 𝒜' ⥤ 𝒮'} {R' : 𝒮' ⥤ 𝒜'} (adj : L ⊣ R) (adj' : L' ⊣ R')
  {G : 𝒜 ⥤ 𝒜'} {H : 𝒮 ⥤ 𝒮'}

/-- The adjoint of `s ≫ G(z) ≫ θ` for `θ = β(Q) ≫ R'(σ⁻¹)` and `β` the mate of `ν`: it is
`σ⁻¹ ∘ H(z^♭) ∘ ν(P) ∘ L'(s)`. -/
lemma homEquiv_symm_comp_map_comp_mateEquiv (ν : G ⋙ L' ⟶ L ⋙ H) {P : 𝒜} {Q : 𝒮} {P' : 𝒜'}
    {Q' : 𝒮'} (σ : Q' ⟶ H.obj Q) [IsIso σ] (s : P' ⟶ G.obj P) (z : P ⟶ R.obj Q) :
    (adj'.homEquiv _ _).symm (s ≫ G.map z ≫ (mateEquiv adj adj' ν).app Q ≫ R'.map (inv σ)) =
      L'.map s ≫ ν.app P ≫ H.map ((adj.homEquiv _ _).symm z) ≫ inv σ := by
  have h₁ := mateEquiv_counit adj adj' ν Q
  have h₂ := ν.naturality z
  simp only [Functor.comp_obj, Functor.comp_map] at h₁ h₂
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [adj'.counit_naturality, reassoc_of% h₁, reassoc_of% h₂]

end Abstract

variable {ℓ : ℕ} [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {k' : Type u} [Field k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

section Composition

variable (ℓ) {F X : Over (Spec (.of k))} [LocallyOfFiniteType F.hom] [QuasiCompact F.hom]
  [IsSeparated F.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {F' X' : Over (Spec (.of k'))} [LocallyOfFiniteType F'.hom] [QuasiCompact F'.hom]
  [IsSeparated F'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  {ΨF : Dᵇc(F.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(F'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {ΨX : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {Ψpt : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
    Dᵇc((point k').left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  (σpt : 𝟙_ _ ⟶ Ψpt.obj (𝟙_ _)) [IsIso σpt]

/-- The composition law `θ_F = d'^! θ_X ∘ β_d(ω_X)` (`dualizingExchange_eq_comp`) for the
composite `compExchange` of the compact-support exchanges `ν_d` and `ν_X`. -/
theorem dualizingExchange_compExchange (d : F ⟶ X) (d' : F' ⟶ X')
    (νd : ΨF ⋙ boundedConstructibleLowerShriek ℓ d' ⟶
      boundedConstructibleLowerShriek ℓ d ⋙ ΨX)
    (νX : ΨX ⋙ boundedConstructibleLowerShriek ℓ (toPoint X') ⟶
      boundedConstructibleLowerShriek ℓ (toPoint X) ⋙ Ψpt) :
    dualizingExchange ℓ σpt (compExchange (lowerShriekCompOfEq ℓ d (toPoint X) (comp_toPoint d))
        (lowerShriekCompOfEq ℓ d' (toPoint X') (comp_toPoint d')) νd νX) =
      ΨF.map (dualizingComplexComp ℓ d).inv ≫
      (exceptionalExchange ℓ d d' νd).app (dualizingComplex' ℓ X) ≫
      (boundedConstructibleUpperShriek ℓ d').map
        (dualizingExchange ℓ σpt νX) ≫ (dualizingComplexComp ℓ d').hom :=
  dualizingExchange_eq_comp ℓ σpt d d' νd νX _ (compExchange_app_comp _ _ νd νX)

end Composition

namespace BorelMooreSection

variable (ℓ) (X : Over (Spec (.of k))) [QuasiCompact X.hom] [IsProper X.hom]

/-- The *unit class* `ℚ̄_ℓ,s ⟶ Ra_{X!} ℚ̄_ℓ,X` of a scheme proper over `s`: the unit of
`La_X^* ⊣ Ra_{X*}` at `ℚ̄_ℓ`, read through the unit isomorphism of the monoidal functor `La_X^*`
and the identification `Ra_{X!} ≅ Ra_{X*}`. The integral of a Borel–Moore section `α` is the
adjoint `α^♭ : Ra_{X!} ℚ̄_ℓ ⟶ ℚ̄_ℓ` of `α` precomposed with the unit class
(`ProEtale.CondensedRing.BorelMooreSection.integral_eq`). -/
noncomputable def unitClass :
    𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) ⟶
      (boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        (𝟙_ _) :=
  haveI : IsProper (toPoint X).left := by rw [toPoint_left]; infer_instance
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ
      (toPoint X)).unit.app (𝟙_ _) ≫
    (boundedConstructibleLowerStar ℓ (toPoint X)).map
      (Functor.Monoidal.εIso
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X))).inv ≫
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint X)).inv.app (𝟙_ _)

variable {ℓ X}

lemma integral_eq (α : BorelMooreSection ℓ X) :
    α.integral.asHom = unitClass ℓ X ≫
      ((boundedConstructibleUpperShriekAdjunction ℓ
        (toPoint X)).homEquiv _ _).symm α := by
  simp only [integral, unitClass, Category.assoc]

end BorelMooreSection

namespace Correspondence

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {K' : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {c : Correspondence ℓ K} {F : c.FixedLocus} {c' : Correspondence ℓ K'} {F' : c'.FixedLocus}

namespace TraceSpecialization

variable (T : c.TraceSpecialization F c' F')
  {Ψpt : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
    Dᵇc((point k').left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  (σpt : 𝟙_ _ ⟶ Ψpt.obj (𝟙_ _)) [IsIso σpt]

/-- **The integral of a specialized section**: if `θ_F` is the dualizing map of a compact-support
exchange `ν_F` and `F'` is proper, then
`∫_{F'} sp_F(z) = σ_s⁻¹ ∘ Ψ_s(z^♭) ∘ ν_F(ℚ̄_ℓ) ∘ Ra_{F'!}(σ_F) ∘ [F']`. -/
theorem integral_sp_eq [IsProper F'.F.hom]
    (νF : T.ΨF ⋙ boundedConstructibleLowerShriek ℓ
        (toPoint F'.F) ⟶
      boundedConstructibleLowerShriek ℓ (toPoint F.F) ⋙ Ψpt)
    (hθ : T.θF = dualizingExchange ℓ σpt νF) (z : BorelMooreSection ℓ F.F) :
    (T.sp z).integral.asHom = BorelMooreSection.unitClass ℓ F'.F ≫
      (boundedConstructibleLowerShriek ℓ (toPoint F'.F)).map
        T.σF ≫ νF.app (𝟙_ (Dᵇc(F.F.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) ≫
      Ψpt.map (((boundedConstructibleUpperShriekAdjunction ℓ
        (toPoint F.F)).homEquiv _ _).symm z) ≫ inv σpt := by
  rw [BorelMooreSection.integral_eq, sp, hθ]
  exact congrArg _ (homEquiv_symm_comp_map_comp_mateEquiv
    (boundedConstructibleUpperShriekAdjunction ℓ (toPoint F.F))
    (boundedConstructibleUpperShriekAdjunction ℓ (toPoint F'.F))
    νF σpt T.σF z)


section OfSupportExchange

variable (ΨC : Dᵇc(c.C.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
    Dᵇc(c'.C.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (ΨX : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (ΨXX : Dᵇc((X ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
    Dᵇc((X' ⨯ X').left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (χΔ : boundedConstructibleLowerStar ℓ (diag X) ⋙ ΨXX ⟶
    ΨX ⋙ boundedConstructibleLowerStar ℓ (diag X'))
  (βc : boundedConstructibleUpperShriek ℓ c.support ⋙ ΨC ⟶
    ΨXX ⋙ boundedConstructibleUpperShriek ℓ c'.support)
  (σC : 𝟙_ _ ⟶ ΨC.obj (𝟙_ _))
  (νX : ΨX ⋙ boundedConstructibleLowerShriek ℓ (toPoint X') ⟶
    boundedConstructibleLowerShriek ℓ (toPoint X) ⋙ Ψpt)

/-- The compact-support exchange `ν_d : Rd'_! Ψ_F ⟶ Ψ_X Rd_!` whose mate is the exceptional
exchange `β_d` determined by the support (`fixedLocusExceptionalExchange`). -/
noncomputable def fixedLocusCompactSupportExchange :
    fixedLocusSpecialization (F := F) (F' := F') ΨC ⋙
        boundedConstructibleLowerShriek ℓ F'.d ⟶
      boundedConstructibleLowerShriek ℓ F.d ⋙ ΨX :=
  (CategoryTheory.mateEquiv (boundedConstructibleUpperShriekAdjunction ℓ F.d)
    (boundedConstructibleUpperShriekAdjunction ℓ F'.d)).symm
    (fixedLocusExceptionalExchange (F := F) (F' := F') ΨC ΨX ΨXX χΔ βc)

lemma exceptionalExchange_fixedLocusCompactSupportExchange :
    exceptionalExchange ℓ F.d F'.d
        (fixedLocusCompactSupportExchange (F := F) (F' := F') ΨC ΨX ΨXX χΔ βc) =
      fixedLocusExceptionalExchange (F := F) (F' := F') ΨC ΨX ΨXX χΔ βc :=
  Equiv.apply_symm_apply _ _

/-- The compact-support exchange `ν_F : Ra_{F'!} Ψ_F ⟶ Ψ_s Ra_{F!}` of the structure maps of the
fixed loci: the composite of `ν_d` (`fixedLocusCompactSupportExchange`) and `ν_X`, read through
the composition isomorphisms `Ra_{F!} ≅ Ra_{X!} Rd_!`. -/
noncomputable abbrev fixedLocusToPointCompactSupportExchange :
    fixedLocusSpecialization (F := F) (F' := F') ΨC ⋙
        boundedConstructibleLowerShriek ℓ (toPoint F'.F) ⟶
      boundedConstructibleLowerShriek ℓ (toPoint F.F) ⋙ Ψpt :=
  compExchange (lowerShriekCompOfEq ℓ F.d (toPoint X) (comp_toPoint F.d))
    (lowerShriekCompOfEq ℓ F'.d (toPoint X') (comp_toPoint F'.d))
    (fixedLocusCompactSupportExchange (F := F) (F' := F') ΨC ΨX ΨXX χΔ βc) νX

/-- **The dualizing map of the fixed locus is the dualizing map of `ν_F`** (blueprint
`lemma-compatibilities-base-change-maps` (3)): for the specialization data determined by the support
with `θ_X` the dualizing map of `ν_X`, `θ_F` is the dualizing map of
`fixedLocusToPointCompactSupportExchange`. -/
theorem θF_ofSupportExchange :
    (ofSupportExchange (F := F) (F' := F') ΨC ΨX ΨXX χΔ βc σC (dualizingExchange ℓ σpt νX)).θF =
      dualizingExchange ℓ σpt (fixedLocusToPointCompactSupportExchange ΨC ΨX ΨXX χΔ βc νX) := by
  rw [fixedLocusToPointCompactSupportExchange, dualizingExchange_compExchange,
    exceptionalExchange_fixedLocusCompactSupportExchange]
  rfl

end OfSupportExchange

end TraceSpecialization

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
