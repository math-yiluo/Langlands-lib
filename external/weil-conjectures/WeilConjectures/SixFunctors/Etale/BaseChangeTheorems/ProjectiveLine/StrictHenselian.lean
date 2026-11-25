/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
public import WeilConjectures.CategoryTheory.Sites.CoinduceZMod
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyModules
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.FiniteLowerStarLift
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.BaseChange.DerivedForget
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Forget
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMapDevissage
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.StrictLocalTotalCohomologyExchange
import WeilConjectures.AlgebraicGeometry.CohomologyRestrictionSquareTransport
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.AlgebraicGeometry.AffineClosedInjectiveAcyclic
import WeilConjectures.AlgebraicGeometry.FiniteAffineCoverRestrictionBound
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
import WeilConjectures.AlgebraicGeometry.ConstructibleRestrictionClass
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding
import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale
import WeilConjectures.SixFunctors.BaseChange.Derived

/-!
# The projective line over a henselian local ring

Let `A` be a henselian local ring with residue field `κ`, let `X = ℙ¹_A` and let
`X₀ = ℙ¹_κ` be its closed fibre, with closed immersion `ι : X₀ ⟶ X` (the base change of
`Spec κ ⟶ Spec A`). For a sheaf `F` on `X_ét` write `F₀ = ι⁻¹ F`. This file records the
comparison between the cohomology of `X` and of `X₀`:

* for an injective sheaf `I` of `𝔽_r`-modules on `X`, the restriction `I₀` has no higher
  cohomology on `X₀`; in degrees `≥ 2` this is a general bound for schemes over a henselian
  pair covered by finitely many affine opens, and in degree `1` it uses the representation of
  `H¹`-classes through finite pushforwards of constant sheaves together with the `H¹`
  comparison for finite constant sheaves;
* restriction `Hᵠ(X, F) ⟶ Hᵠ(X₀, F₀)` is bijective for every torsion sheaf `F`;
* for a local morphism `A ⟶ B` of strictly henselian local rings, the stalk at the closed
  geometric point of the exchange morphism of `ℙ¹` is the pullback map between the
  cohomologies of the two closed fibres.

The coefficients `𝔽_r` are `ZMod r` with `r` prime; a sheaf of `𝔽_r`-modules is a sheaf of
`ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))`-modules, following the universe convention of
the `SixFunctors` folder.

## Main statements

- `AlgebraicGeometry.Etale.subsingleton_H_upperStar_of_injective_of_iSup_eq_top`: the
  acyclicity bound for the restriction of an injective sheaf to the closed fibre of a
  separated scheme of finite type over a henselian pair covered by `n + 1` affine opens.
- `AlgebraicGeometry.Etale.exists_sum_eq_of_injective_projectiveLine`: the representation of
  an `H¹`-class of `I₀` by classes of finite pushforwards of constant sheaves.
- `AlgebraicGeometry.Etale.subsingleton_H_projectiveLine_closedFibre_of_injective_of_one_lt`:
  its case of degrees `q ≥ 2`.
- `AlgebraicGeometry.Etale.subsingleton_H_projectiveLine_closedFibre_of_injective`: the
  acyclicity of `I₀` on `ℙ¹_κ`.
- `AlgebraicGeometry.Etale.subsingleton_H_projectiveLine_residueField_of_injective`: an alias
  of the previous statement, recording the `Γ(X₀, -)`-acyclicity of `I₀`.
- `AlgebraicGeometry.Etale.bijective_cohomologyMap_projectiveLine_residueField`: the henselian
  comparison `Hᵠ(ℙ¹_A, F) ≅ Hᵠ(ℙ¹_κ, F₀)`.
- `AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_strictLocal`: the
  strict-local exchange, and
  `AlgebraicGeometry.Etale.isIso_sheafFiber_baseChangeHomologyMap_strictLocal`: its stalk is an
  isomorphism when the residue field map is.

## References

- Stacks Project, Section 59.91, <https://stacks.math.columbia.edu/tag/0A3S>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- **Acyclicity bound for restricted injectives.** Let `(A, I)` be a henselian pair, let
`f : Y ⟶ Spec A` be separated and locally of finite type, and let `i : Y₀ ⟶ Y` be the closed
fibre over `Spec A/I`. Suppose `Y` is covered by `n + 1` affine opens. Then for every
injective torsion sheaf `J` of `Λ`-modules on `Y_ét`, the restriction `J|_{Y₀}` has vanishing
cohomology in degrees `q > n`.

Here torsion is required, as in Gabber's affine comparison, which is the input of the case
`n = 0`; the induction on `n` is the Mayer–Vietoris sequence of the closed fibre.
(blueprint: lemma-acyclicity-closed-fibre--1)
-/
theorem Etale.subsingleton_H_upperStar_of_injective_of_iSup_eq_top
    (Λ : Type (u + 1)) [CommRing Λ] {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    {Y Y₀ : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [LocallyOfFiniteType f] [IsSeparated f]
    (i : Y₀ ⟶ Y) (f₀ : Y₀ ⟶ Spec (.of (A ⧸ I)))
    (h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    (n : ℕ) (U : Fin (n + 1) → Y.Opens) (hU : ∀ j, IsAffineOpen (U j)) (hcov : ⨆ j, U j = ⊤)
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J] [IsTorsionModuleSheaf J]
    (q : ℕ) (hq : n < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
      ((i)^*[ModuleCat.{u + 1} Λ].obj J)) q) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.mk_surjective)
  have : IsClosedImmersion i :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip inferInstance
  apply Etale.subsingleton_H_of_affine_local_acyclic Λ f i J _ n U hU hcov q hq
  intro W hW k hk
  let : IsAffine W.toScheme := hW
  let : Injective ((W.ι)^*[ModuleCat.{u + 1} Λ].obj J) :=
    Etale.injective_upperStar_obj_of_etale Λ W.ι J
  exact Etale.subsingleton_H_affine_closed_of_injective Λ (pullback.fst W.ι i)
    ((W.ι)^*[ModuleCat.{u + 1} Λ].obj J) k hk

section HenselianLocal

variable (A : Type u) [CommRing A] [HenselianLocalRing A]

/-- **Representation of an `H¹`-class of a restricted injective.** Let `A` be henselian
local, `X = ℙ¹_A`, `ι : X₀ = ℙ¹_κ ⟶ X` the closed fibre, `r` a prime and `I` an injective
sheaf of `𝔽_r`-modules on `X`. Every class `c ∈ H¹(X₀, I₀)` is a finite sum
`c = ∑ⱼ ψⱼ(xⱼ)` of images of classes `xⱼ ∈ H¹(X₀, ((hⱼ)_* Mⱼ)₀)`, where `hⱼ : Vⱼ ⟶ X` is finite
and of finite presentation, `Mⱼ` is a finite `𝔽_r`-module with constant sheaf `Mⱼ` on `Vⱼ`,
and `ψⱼ : (hⱼ)_* Mⱼ ⟶ I` is a morphism of sheaves. (Equivalently `c` is the image of a class
of `H¹(X₀, (⊕ⱼ (hⱼ)_* Mⱼ)₀)` under a map `⊕ⱼ (hⱼ)_* Mⱼ ⟶ I`.)
(blueprint: lemma-acyclicity-closed-fibre--1)
-/
theorem Etale.exists_sum_eq_of_injective_projectiveLine (r : ℕ) [Fact r.Prime]
    (I : Sheaf (ProjectiveLine (Spec (.of A))).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) [Injective I]
    (c : Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
      AddCommGrpCat.{u + 1})).obj ((ProjectiveSpace.map _
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))^*[ModuleCat.{u + 1}
          (ULift.{u + 1} (ZMod r))].obj I)) 1) :
    ∃ (n : ℕ) (V : Fin n → Scheme.{u}) (h : ∀ j, V j ⟶ ProjectiveLine (Spec (.of A)))
      (_ : ∀ j, IsFinite (h j)) (_ : ∀ j, LocallyOfFinitePresentation (h j))
      (M : Fin n → ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) (_ : ∀ j, Finite (M j))
      (ψ : ∀ j, (h j)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))].obj
        ((constantSheaf (V j).smallEtaleTopology _).obj (M j)) ⟶ I)
      (x : ∀ j, Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
        AddCommGrpCat.{u + 1})).obj ((ProjectiveSpace.map _
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))^*[ModuleCat.{u + 1}
            (ULift.{u + 1} (ZMod r))].obj ((h j)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))].obj
              ((constantSheaf (V j).smallEtaleTopology _).obj (M j))))) 1),
      ∑ j, Sheaf.H.map ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
        AddCommGrpCat.{u + 1})).map ((ProjectiveSpace.map _
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))^*[ModuleCat.{u + 1}
            (ULift.{u + 1} (ZMod r))].map (ψ j))) 1 (x j) = c := by
  classical
  have : CompactSpace (ProjectiveLine (Spec (.of A))) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A))
  have : QuasiSeparatedSpace (ProjectiveLine (Spec (.of A))) :=
    quasiSeparatedSpace_of_quasiSeparated (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A))
  have : CompactSpace (ProjectiveLine (Spec (.of (IsLocalRing.ResidueField A)))) :=
    QuasiCompact.compactSpace_of_compactSpace
      (ProjectiveLine (Spec (.of (IsLocalRing.ResidueField A))) ↘
        Spec (.of (IsLocalRing.ResidueField A)))
  have : QuasiSeparatedSpace (ProjectiveLine (Spec (.of (IsLocalRing.ResidueField A)))) :=
    quasiSeparatedSpace_of_quasiSeparated
      (ProjectiveLine (Spec (.of (IsLocalRing.ResidueField A))) ↘
        Spec (.of (IsLocalRing.ResidueField A)))
  let Λ := ULift.{u + 1} (ZMod r)
  let i := ProjectiveSpace.map (ULift.{u} (Fin 2))
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))
  have : (sheafCompose
      (ProjectiveLine (Spec (.of (IsLocalRing.ResidueField A)))).smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).Additive :=
    ⟨by intros; rfl⟩
  let T := (i)^*[ModuleCat.{u + 1} Λ] ⋙
    sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  obtain ⟨G, hG, a, z, hz⟩ := Etale.exists_constructible_restriction_class i Λ I 1 c
  obtain ⟨n, V, h, hh, hfp, M, hM, ι, hι⟩ :=
    Etale.finite_pushforward_embedding_of_isConstructibleEtaleModuleSheaf Λ G hG
  let E (j : Fin n) := (h j)_*[ModuleCat.{u + 1} Λ].obj
    ((constantSheaf (V j).smallEtaleTopology _).obj (M j))
  let := hι
  let ψ := Injective.factorThru a ι
  let z' := Sheaf.H.map (T.map ι) 1 z
  refine ⟨n, V, h, hh, hfp, M, hM,
    (fun j ↦ biproduct.ι E j ≫ ψ),
    (fun j ↦ Sheaf.H.map (T.map (biproduct.π E j)) 1 z'), ?_⟩
  change ∑ j, Sheaf.H.map (T.map (biproduct.ι E j ≫ ψ)) 1
    (Sheaf.H.map (T.map (biproduct.π E j)) 1 z') = c
  simp_rw [← Sheaf.H.map_comp_apply, ← T.map_comp, ← Category.assoc]
  let H := T ⋙ Sheaf.functorH _ 1
  have he : ∑ j, H.map (biproduct.π E j ≫ biproduct.ι E j ≫ ψ) = H.map ψ := by
    rw [← H.map_sum]
    simp only [← Category.assoc]
    rw [← Preadditive.sum_comp, IsBilimit.total (biproduct.isBilimit E), Category.id_comp]
  dsimp [H] at he
  have he' := congrArg (fun f ↦ AddCommGrpCat.homAddEquiv f z') he
  rw [map_sum, AddMonoidHom.finsetSum_apply] at he'
  change ∑ j, Sheaf.H.map (T.map (biproduct.π E j ≫ biproduct.ι E j ≫ ψ)) 1 z' =
    Sheaf.H.map (T.map ψ) 1 z' at he'
  simp only [Category.assoc]
  rw [he']
  dsimp [z']
  rw [← Sheaf.H.map_comp_apply, ← T.map_comp, Injective.comp_factorThru]
  exact hz

/-- **Acyclicity on the closed projective line in degrees at least two.** Let `A` be henselian
local, `X = ℙ¹_A`, `ι : X₀ = ℙ¹_κ ⟶ X` the closed fibre and `r` a prime. For every injective
sheaf `I` of `𝔽_r`-modules on `X`, `Hᵠ(X₀, I₀) = 0` for `q ≥ 2`: this is the acyclicity bound
`AlgebraicGeometry.Etale.subsingleton_H_upperStar_of_injective_of_iSup_eq_top` for the cover of
`ℙ¹_A` by its two standard affine opens. This is the first step of the proof of the blueprint
node `lemma-acyclicity-closed-fibre--1`. -/
theorem Etale.subsingleton_H_projectiveLine_closedFibre_of_injective_of_one_lt (r : ℕ)
    [Fact r.Prime] (I : Sheaf (ProjectiveLine (Spec (.of A))).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) [Injective I] (q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
      AddCommGrpCat.{u + 1})).obj ((ProjectiveSpace.map _
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))^*[ModuleCat.{u + 1}
          (ULift.{u + 1} (ZMod r))].obj I)) q) :=
  Etale.subsingleton_H_upperStar_of_injective_of_iSup_eq_top (ULift.{u + 1} (ZMod r))
    (IsLocalRing.maximalIdeal A) (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A))
    (ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))
    (show _ ⟶ Spec (.of (IsLocalRing.ResidueField A)) from
      ProjectiveLine (Spec (.of (IsLocalRing.ResidueField A))) ↘ _)
    (ProjectiveSpace.isPullback_map _ _) 1
    (fun j ↦ ProjectiveSpace.standardOpen _ _ (ULift.up j))
    (fun j ↦ ProjectiveSpace.isAffineOpen_standardOpen _ _ _)
    (by
      rw [← ProjectiveSpace.iSup_standardOpen _ (Spec (.of A))]
      exact Equiv.ulift.symm.iSup_comp (g := ProjectiveSpace.standardOpen _ _))
    I q hq

/-- **Acyclicity on the closed projective line.** Let `A` be henselian local, `X = ℙ¹_A`,
`ι : X₀ = ℙ¹_κ ⟶ X` the closed fibre and `r` a prime. For every injective sheaf `I` of
`𝔽_r`-modules on `X`, `Hᵠ(X₀, I₀) = 0` for `q > 0`. Degrees `q ≥ 2` are
`AlgebraicGeometry.Etale.subsingleton_H_projectiveLine_closedFibre_of_injective_of_one_lt`. In
degree `1`, write a class as `∑ⱼ ψⱼ(xⱼ)` with `xⱼ ∈ H¹(X₀, ((hⱼ)_* Mⱼ)₀)`
(`AlgebraicGeometry.Etale.exists_sum_eq_of_injective_projectiveLine`); each `xⱼ` lifts to
`H¹(X, (hⱼ)_* Mⱼ)`
(`AlgebraicGeometry.Etale.surjective_cohomologyMap_one_lowerStar_constantSheaf`),
and its image in `H¹(X, I)` vanishes since the underlying abelian sheaf of `I` is acyclic
(`CategoryTheory.Sheaf.subsingleton_H_forget₂_of_injective`).
(blueprint: lemma-acyclicity-closed-fibre--1)
-/
theorem Etale.subsingleton_H_projectiveLine_closedFibre_of_injective (r : ℕ) [Fact r.Prime]
    (I : Sheaf (ProjectiveLine (Spec (.of A))).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) [Injective I] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
      AddCommGrpCat.{u + 1})).obj ((ProjectiveSpace.map _
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))^*[ModuleCat.{u + 1}
          (ULift.{u + 1} (ZMod r))].obj I)) q) := by
  obtain rfl | hq := (Nat.one_le_iff_ne_zero.2 hq.ne').eq_or_lt
  · set ι := ProjectiveSpace.map (ULift.{u} (Fin 2))
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))
    let Λ := ULift.{u + 1} (ZMod r)
    let fo := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
    let e := (asIso (upperStarForget₂ Λ ι)).symm
    refine ⟨fun c₁ c₂ ↦ ?_⟩
    suffices ∀ c : Sheaf.H ((sheafCompose _ fo).obj ((ι)^*[ModuleCat.{u + 1} Λ].obj I)) 1,
        c = 0 by rw [this c₁, this c₂]
    intro c
    obtain ⟨n, V, h, hfin, -, M, hM, ψ, x, rfl⟩ :=
      Etale.exists_sum_eq_of_injective_projectiveLine A r I c
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    let G := (h j)_*[ModuleCat.{u + 1} Λ].obj
      ((constantSheaf (V j).smallEtaleTopology _).obj (M j))
    let β : (sheafCompose _ fo).obj G ≅ ((h j)_*[AddCommGrpCat.{u + 1}]).obj
        ((constantSheaf (V j).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (M j))) :=
      (lowerStarCompForget₂Iso Λ (h j)).app _ ≪≫
        ((h j)_*[AddCommGrpCat.{u + 1}]).mapIso
          ((constantSheafSheafComposeForget₂Iso (Y := V j) Λ).app (M j))
    have hS := surjective_cohomologyMap_one_lowerStar_constantSheaf
      (IsLocalRing.maximalIdeal A) (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A)) ι
      (show _ ⟶ Spec (.of (IsLocalRing.ResidueField A)) from
        ProjectiveLine (Spec (.of (IsLocalRing.ResidueField A))) ↘ _)
      (ProjectiveSpace.isPullback_map _ _) (h j) (pullback.fst (h j) ι)
      (pullback.snd (h j) ι) (IsPullback.of_hasPullback _ _) (M j)
    obtain ⟨z, hz⟩ := hS (Sheaf.H.map ((ι)^*[AddCommGrpCat.{u + 1}].map β.hom) 1
      (Sheaf.H.map ((e.app G).hom) 1 (x j)))
    have hx : x j = Sheaf.H.map (e.app G).inv 1
        (cohomologyMap ι ((sheafCompose _ fo).obj G) 1 (Sheaf.H.map β.inv 1 z)) := by
      rw [cohomologyMap_map, hz, ← Sheaf.H.map_comp_apply, ← Functor.map_comp,
        Iso.hom_inv_id, CategoryTheory.Functor.map_id, Sheaf.H.map_id_apply,
        ← Sheaf.H.map_comp_apply, Iso.hom_inv_id, Sheaf.H.map_id_apply]
    have : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩
    have hI := CategoryTheory.Sheaf.subsingleton_H_forget₂_of_injective.{u + 1, u + 1, u, u + 1}
      Λ I 0
    have hψ : (e.app G).inv ≫ (sheafCompose _ fo).map ((ι)^*[ModuleCat.{u + 1} Λ].map (ψ j)) =
        (ι)^*[AddCommGrpCat.{u + 1}].map ((sheafCompose _ fo).map (ψ j)) ≫ (e.app I).inv :=
      (e.inv.naturality (ψ j)).symm
    rw [hx]
    refine (Sheaf.H.map_comp_apply (f := (e.app G).inv) _ _).symm.trans ?_
    rw [hψ, Sheaf.H.map_comp_apply]
    refine (congrArg (Sheaf.H.map (e.app I).inv 1)
      (cohomologyMap_map ι 1 ((sheafCompose _ fo).map (ψ j)) _).symm).trans ?_
    rw [Subsingleton.elim (Sheaf.H.map ((sheafCompose _ fo).map (ψ j)) 1 _) 0,
      map_zero, map_zero]
  exact Etale.subsingleton_H_projectiveLine_closedFibre_of_injective_of_one_lt A r I q hq

/-- **Acyclicity of injectives on `ℙ¹_κ`.** Let `A` be henselian local, `X = ℙ¹_A` and
`ι : X₀ = ℙ¹_κ ⟶ X` the closed fibre. For a prime `ℓ` and an injective sheaf `I` of
`𝔽_ℓ`-modules on `X`, the restriction `I₀` is `Γ(X₀, -)`-acyclic: `Hᵠ(X₀, I₀) = 0` for all
`q > 0`. In Lean this is the same statement as
`AlgebraicGeometry.Etale.subsingleton_H_projectiveLine_closedFibre_of_injective`.
(blueprint: `lemma-acyclicity-closed-fibre--1`) -/
alias Etale.subsingleton_H_projectiveLine_residueField_of_injective :=
  Etale.subsingleton_H_projectiveLine_closedFibre_of_injective

/-- **The comparison for `ℙ¹` in degree zero.** For every étale sheaf `F` of `Λ`-modules on
`ℙ¹_A`, restriction `Γ(ℙ¹_A, F) ⟶ Γ(ℙ¹_κ, F₀)` is bijective: `ℙ¹_A` is proper over the
henselian local ring `A`, so this is
`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_of_henselianRing`. -/
theorem Etale.bijective_cohomologyMap_zero_projectiveLine_residueField
    (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf (ProjectiveLine (Spec (.of A))).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Function.Bijective (Etale.cohomologyMap
      (ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) 0) :=
  (Etale.bijective_cohomologyMap_zero_iff _ _).2
    ((Etale.isIso_globalSectionsUpperStarMap_iff_forget₂ Λ _ F).1
      (Etale.isIso_globalSectionsUpperStarMap_of_henselianRing Λ (IsLocalRing.maximalIdeal A)
        (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A))
        (ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))
        (show _ ⟶ Spec (.of (IsLocalRing.ResidueField A)) from
          ProjectiveLine (Spec (.of (IsLocalRing.ResidueField A))) ↘ _)
        (ProjectiveSpace.isPullback_map _ _) F))

open Abelian in
/-- **The comparison for `ℙ¹` with `𝔽_r`-coefficients.** For a prime `r` and every sheaf `F`
of `𝔽_r`-modules on `ℙ¹_A`, restriction `Hᵠ(ℙ¹_A, F) ⟶ Hᵠ(ℙ¹_κ, F₀)` is bijective. By
induction on `q`, embedding `F` into an injective sheaf `I` of `𝔽_r`-modules: the underlying
abelian sheaves of `I` and of `I₀` have no higher cohomology
(`CategoryTheory.Sheaf.subsingleton_H_forget₂_of_injective` and
`AlgebraicGeometry.Etale.subsingleton_H_projectiveLine_closedFibre_of_injective`), and a
diagram chase in the long exact sequences of `0 ⟶ F ⟶ I ⟶ I/F ⟶ 0` on `ℙ¹_A` and `ℙ¹_κ`
concludes. -/
theorem Etale.bijective_cohomologyMap_projectiveLine_residueField_zmod (r : ℕ) [Fact r.Prime]
    (F : Sheaf (ProjectiveLine (Spec (.of A))).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap
      (ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
        AddCommGrpCat.{u + 1})).obj F) q) := by
  set ι := ProjectiveSpace.map (ULift.{u} (Fin 2))
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))
  let Λ := ULift.{u + 1} (ZMod r)
  let fo := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩
  induction q generalizing F with
  | zero => exact Etale.bijective_cohomologyMap_zero_projectiveLine_residueField A Λ F
  | succ n ih =>
    let i := Injective.ι F
    let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
    have hS : (S.map (sheafCompose _ fo)).ShortExact :=
      shortExact_map_forget₂ Λ { exact := ShortComplex.exact_cokernel i }
    have hS₀ := hS.map_of_exact ((ι)^*[AddCommGrpCat.{u + 1}])
    have hI : Subsingleton (Sheaf.H ((sheafCompose _ fo).obj (Injective.under F)) (n + 1)) :=
      CategoryTheory.Sheaf.subsingleton_H_forget₂_of_injective.{u + 1, u + 1, u, u + 1} Λ _ n
    have hI₀ : Subsingleton (Sheaf.H ((ι)^*[AddCommGrpCat.{u + 1}].obj
        ((sheafCompose _ fo).obj (Injective.under F))) (n + 1)) := by
      have := Etale.subsingleton_H_projectiveLine_closedFibre_of_injective A r
        (Injective.under F) (n + 1) n.succ_pos
      exact ⟨fun a b ↦ (bijective_sheafHMap_hom
        ((asIso (upperStarForget₂ Λ ι)).app (Injective.under F)) _).1
          (@Subsingleton.elim _ this _ _)⟩
    refine ⟨?_, fun η ↦ ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro ξ hξ
      obtain ⟨z, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS ξ (@Subsingleton.elim _ hI _ _) rfl
      replace hξ := (cohomologyMap_comp_extClass _ hS z).symm.trans hξ
      obtain ⟨w, hw⟩ := Ext.covariant_sequence_exact₃ _ hS₀ _ rfl hξ
      obtain ⟨v, rfl⟩ := (ih _).2 w
      have hvz : v.comp (Ext.mk₀ (S.map (sheafCompose _ fo)).g) (add_zero n) = z :=
        (ih (cokernel i)).1 ((cohomologyMap_comp_mk₀ _ _ v).trans hw)
      rw [← hvz, Ext.comp_assoc _ _ _ (add_zero n) (zero_add 1) (by omega)]
      exact (congrArg (fun t ↦ v.comp t (show n + 1 = n + 1 from rfl)) hS.comp_extClass).trans
        (Ext.comp_zero _ _ _ _ _)
    · obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ hS₀ η (@Subsingleton.elim _ hI₀ _ _) rfl
      obtain ⟨z, rfl⟩ := (ih (cokernel i)).2 y
      exact ⟨z.comp hS.extClass rfl, (cohomologyMap_comp_extClass _ hS z).trans hy⟩

/-- **The henselian comparison for `ℙ¹`.** Let `A` be henselian local with
residue field `κ` and `ι : ℙ¹_κ ⟶ ℙ¹_A` the closed fibre. For every torsion sheaf `F` of
`Λ`-modules on `ℙ¹_A` and every `q ≥ 0`, restriction `Hᵠ(ℙ¹_A, F) ⟶ Hᵠ(ℙ¹_κ, F₀)` is
bijective.
(blueprint: proposition-cohomology-p-1-over-henselian--1)
-/
theorem Etale.bijective_cohomologyMap_projectiveLine_residueField
    (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf (ProjectiveLine (Spec (.of A))).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap
      (ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) := by
  let p := ProjectiveLine (Spec (.of A)) ↘ Spec (.of A)
  let p₀ := ProjectiveLine (Spec (.of (IsLocalRing.ResidueField A))) ↘
    Spec (.of (IsLocalRing.ResidueField A))
  have : CompactSpace (ProjectiveLine (Spec (.of A))) :=
    QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace (ProjectiveLine (Spec (.of A))) :=
    quasiSeparatedSpace_of_quasiSeparated p
  have : CompactSpace (ProjectiveLine (Spec (.of (IsLocalRing.ResidueField A)))) :=
    QuasiCompact.compactSpace_of_compactSpace p₀
  have : QuasiSeparatedSpace (ProjectiveLine (Spec (.of (IsLocalRing.ResidueField A)))) :=
    quasiSeparatedSpace_of_quasiSeparated p₀
  refine bijective_cohomologyMap_of_isTorsion _ (fun r hr G hG q ↦ ?_) _
    ((isTorsionModuleSheaf_iff_isTorsion F).1 inferInstance) q
  have : Fact r.Prime := ⟨hr⟩
  have : (coindZMod.{u + 1} r).IsRightAdjoint := (forget₂CoindZModAdj r).isRightAdjoint
  have : PreservesLimitsOfSize.{u, u + 1} (coindZMod.{u + 1} r) :=
    (forget₂CoindZModAdj r).rightAdjoint_preservesLimits
  have : IsIso (CategoryTheory.Sheaf.coindCounit _ r G) := by
    have : IsIso (CategoryTheory.Sheaf.coindCounit _ r G).hom := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro U
      have hU := forget₂CoindZModAdj_counit_shortExact.{u + 1} r (G.obj.obj U)
      refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨hU.1, fun a ↦ hU.2 a ?_⟩
      have h1 := congr(((sheafToPresheaf _ _).map $hG).app U a)
      simp only [Functor.map_nsmul, NatTrans.app_nsmul, Functor.map_zero, NatTrans.app_zero,
        AddCommGrpCat.hom_nsmul, AddCommGrpCat.hom_zero, AddMonoidHom.nsmul_apply,
        AddMonoidHom.zero_apply] at h1
      rw [natCast_zsmul]
      exact h1
    have : IsIso ((sheafToPresheaf _ _).map (CategoryTheory.Sheaf.coindCounit _ r G)) := this
    exact isIso_of_fully_faithful (sheafToPresheaf _ _) _
  exact bijective_cohomologyMap_of_iso _ (asIso (CategoryTheory.Sheaf.coindCounit _ r G)) q
    (Etale.bijective_cohomologyMap_projectiveLine_residueField_zmod A r _ q)

end HenselianLocal

section StrictLocalExchange

variable (Λ : Type (u + 1)) [CommRing Λ]
  {A B : Type u} [CommRing A] [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)]
  [CommRing B] [HenselianLocalRing B] [IsSepClosed (IsLocalRing.ResidueField B)]
  (φ : A →+* B) [IsLocalHom φ]

/-- **The strict-local exchange for `ℙ¹`.** Let `φ : A ⟶ B` be a local morphism of strictly
henselian local rings, with residue fields `κ_A`, `κ_B` and induced map `κ_A ⟶ κ_B`, and
consider the cartesian square
```
ℙ¹_B --g'--> ℙ¹_A
 |            |
 v            v
Spec B -g-> Spec A
```
Let `F` be a torsion sheaf of `Λ`-modules on `ℙ¹_A` and `q ≥ 0`. Then the stalk at the closed
geometric point `Spec κ_B ⟶ Spec B` of the degree-`q` exchange morphism
`g⁻¹ Rᵠp_* F ⟶ Rᵠp'_* g'⁻¹ F` is, up to isomorphisms of its source and target, the pullback
map `Hᵠ(ℙ¹_{κ_A}, F₀) ⟶ Hᵠ(ℙ¹_{κ_B}, F₀|)` along `ℙ¹_{κ_B} ⟶ ℙ¹_{κ_A}`. The isomorphisms are
the strictly henselian comparisons on the two closed fibres.

**Form of the statement.** The statement asserts the existence of additive
isomorphisms of the two stalks with closed-fibre cohomology that make the
exchange square commute.
(blueprint: proposition-proper-base-change-projective-line--1)
-/
theorem Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_strictLocal
    (F : Sheaf (ProjectiveLine (Spec (.of A))).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf F] (q : ℕ) :
    ∃ (e₁ : ((pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeSourceFunctor Λ (Spec.map (CommRingCat.ofHom φ))
            (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A)) q).obj F) ≃+
        Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))^*[
            ModuleCat.{u + 1} Λ].obj F)) q)
      (e₂ : ((pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeTargetFunctor Λ (ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom φ)))
            (ProjectiveLine (Spec (.of B)) ↘ Spec (.of B)) q).obj F) ≃+
        Sheaf.H ((ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom
            (IsLocalRing.ResidueField.map φ))))^*[AddCommGrpCat.{u + 1}].obj
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))^*[
              ModuleCat.{u + 1} Λ].obj F))) q),
      ∀ x, e₂ ((((pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).map (Etale.baseChangeHomologyMap Λ
            (ProjectiveSpace.isPullback_map _ (Spec.map (CommRingCat.ofHom φ))) q F)).hom x) =
        Etale.cohomologyMap (ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom
            (IsLocalRing.ResidueField.map φ))))
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))^*[
              ModuleCat.{u + 1} Λ].obj F)) q (e₁ x) := by
  let g := ProjectiveSpace.map (ULift.{u} (Fin 2))
    (Spec.map (CommRingCat.ofHom φ))
  let i := ProjectiveSpace.map (ULift.{u} (Fin 2))
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))
  let j := ProjectiveSpace.map (ULift.{u} (Fin 2))
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))
  let k := ProjectiveSpace.map (ULift.{u} (Fin 2))
    (Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)))
  have h : j ≫ g = k ≫ i := by
    dsimp [j, g, k, i]
    rw [← ProjectiveSpace.map_comp, ← ProjectiveSpace.map_comp]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  obtain ⟨a₁, a₂, ha⟩ := Etale.exists_addEquiv_strictLocal_totalCohomology_exchange
    Λ φ (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A))
    (ProjectiveLine (Spec (.of B)) ↘ Spec (.of B)) g
    (ProjectiveSpace.isPullback_map _ (Spec.map (CommRingCat.ofHom φ))) F q
  obtain ⟨b₁, b₂, hb⟩ := Etale.exists_addEquiv_cohomology_restrictionSquare
    Λ g i j k h F q
    (Etale.bijective_cohomologyMap_projectiveLine_residueField A Λ F q)
    (Etale.bijective_cohomologyMap_projectiveLine_residueField B Λ
      ((g)^*[ModuleCat.{u + 1} Λ].obj F) q)
  refine ⟨a₁.trans b₁, a₂.trans b₂, ?_⟩
  intro x
  change b₂ (a₂ _) = Etale.cohomologyMap k _ q (b₁ (a₁ x))
  rw [ha, hb]


/-- If the residue field map `κ_A ⟶ κ_B` of a local morphism of strictly henselian local
rings is an isomorphism, the stalk at the closed geometric point of `Spec B` of the
exchange morphism of `ℙ¹` is an isomorphism. This is the second assertion of the
blueprint node `proposition-proper-base-change-projective-line--1`, deduced from
`AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_strictLocal`: the
pullback along the isomorphism `ℙ¹_{κ_B} ⟶ ℙ¹_{κ_A}` is bijective on cohomology. -/
theorem Etale.isIso_sheafFiber_baseChangeHomologyMap_strictLocal
    (hφ : Function.Bijective (IsLocalRing.ResidueField.map φ))
    (F : Sheaf (ProjectiveLine (Spec (.of A))).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf F] (q : ℕ) :
    IsIso (((pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).map (Etale.baseChangeHomologyMap Λ
        (ProjectiveSpace.isPullback_map _ (Spec.map (CommRingCat.ofHom φ))) q F)) := by
  obtain ⟨e₁, e₂, he⟩ := Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_strictLocal
    Λ φ F q
  have : IsIso (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hφ
  have : IsIso (ProjectiveSpace.map (ULift.{u} (Fin 2))
      (Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)))) :=
    ⟨ProjectiveSpace.map _ (inv (Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)))),
      by rw [← ProjectiveSpace.map_comp, IsIso.hom_inv_id, ProjectiveSpace.map_id],
      by rw [← ProjectiveSpace.map_comp, IsIso.inv_hom_id, ProjectiveSpace.map_id]⟩
  rw [ConcreteCategory.isIso_iff_bijective, ← e₂.bijective.of_comp_iff']
  have hfun : e₂ ∘ _ = Etale.cohomologyMap (ProjectiveSpace.map (ULift.{u} (Fin 2))
      (Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ))))
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))^*[
          ModuleCat.{u + 1} Λ].obj F)) q ∘ e₁ := funext he
  rw [hfun]
  exact (Etale.cohomologyMap_bijective _ _ q).comp e₁.bijective

end StrictLocalExchange

end AlgebraicGeometry
