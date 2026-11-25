/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstructibleLimitDescentGeneral
public import WeilConjectures.AlgebraicGeometry.ProperFiniteTypeStage
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProperBaseChangeHomology

/-!
# Constructibility of proper direct images over a Noetherian base

Let `k` be a field and `Λ` a finite ring killed by an integer invertible in `k`. For a proper
morphism `b : Y ⟶ S` with `S` Noetherian over `k`, the higher direct images `Rᵠb_* F` of
constructible sheaves of `Λ`-modules are constructible
(`AlgebraicGeometry.Etale.hasConstructibleDirectImages_of_isProper_of_isNoetherian`).

The question is local on `S`, so `S` may be assumed affine. Then `S` is the limit of the
spectra `Sᵢ` of the finitely generated `k`-subalgebras of `Γ(S, ⊤)`, which are of finite type
over `k`. The morphism `b` and a constructible sheaf `F` on `Y` descend to a proper morphism
`bᵢ : Yᵢ ⟶ Sᵢ` and a constructible sheaf `Fᵢ` on `Yᵢ`
(`AlgebraicGeometry.Etale.exists_isConstructibleSheaf_isPullback_of_isLimit`; Stacks, Tags 01ZM,
081F and 09YU). By proper base change `Rᵠb_* F` is the pullback of `Rᵠ(bᵢ)_* Fᵢ`, which is
constructible by the finite type case
`AlgebraicGeometry.Etale.hasConstructibleDirectImages_of_isProper`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- **Descent of a proper morphism together with a constructible sheaf.** Let `{Dᵢ}` be a
directed inverse system of quasi-compact quasi-separated schemes with affine transition maps and
limit cone `c`, let `b : Y ⟶ lim Dᵢ` be proper and locally of finite presentation, and let `F` be
a constructible sheaf of `Λ`-modules on `Y`. Then at some stage `i` there are a proper morphism
`b' : Y' ⟶ Dᵢ` of which `b` is the base change along `Y ⟶ Y'`, and a constructible sheaf `F'` on
`Y'` whose pullback to `Y` is `F` (Stacks, Tags 01ZM, 081F and 09YU). -/
theorem exists_isConstructibleSheaf_isPullback_of_isLimit {I : Type u} [Preorder I]
    [IsDirectedOrder I] [Nonempty I] {D : Iᵒᵖ ⥤ Scheme.{u}}
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {c : Cone D} (hc : IsLimit c) {Y : Scheme.{u}}
    (b : Y ⟶ c.pt) [IsProper b] [LocallyOfFinitePresentation b]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    ∃ (i : I) (Y' : Scheme.{u}) (b' : Y' ⟶ D.obj (op i)) (g' : Y ⟶ Y')
      (F' : Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsPullback g' b b' (c.π.app (op i)) ∧ IsProper b' ∧ IsConstructibleSheaf F' ∧
        Nonempty ((g')^*[ModuleCat.{u + 1} Λ].obj F' ≅ F) := by
  obtain ⟨l, Y₀, p, h, hp, -, H⟩ := Scheme.exists_isProper_isPullback_of_isLimit hc b
  have : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace Y₀ := quasiSeparatedSpace_of_quasiSeparated p
  obtain ⟨i, F', hF', e⟩ := Scheme.exists_constructible_limit_descent_general
    (baseChangeIciDiagram D l p) (baseChangeIciCone H) (isLimitBaseChangeIciCone hc H) Λ F
  exact ⟨i.1, _, _, _, F', isPullback_baseChangeIciCone H (op i),
    MorphismProperty.pullback_snd _ _ hp, hF', e⟩

/-- **Proper direct images over an affine base over a field.** Let `Λ` be a finite ring killed
by an integer invertible in the field `k`. Every proper morphism `b : Y ⟶ S` locally of finite
presentation, with `S` affine over `k`, satisfies `𝒞(b)`: `b` and a constructible sheaf on `Y`
descend to a proper morphism to a scheme of finite type over `k`, where
`AlgebraicGeometry.Etale.hasConstructibleDirectImages_of_isProper` applies, and proper base
change (`AlgebraicGeometry.Etale.upperStarHomologyRightDerivedLowerStarIsoOfIsProper`)
identifies the higher direct images. -/
theorem hasConstructibleDirectImages_of_isProper_of_isAffine {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))] {Y S : Scheme.{u}} [IsAffine S]
    (aS : S ⟶ Spec (.of k)) (b : Y ⟶ S) [IsProper b] [LocallyOfFinitePresentation b] :
    HasConstructibleDirectImages Λ b := by
  let := algebraΓOfHomSpec aS
  intro F hF q
  obtain ⟨i, Y', b', g', F', H, hb', hF', ⟨e⟩⟩ :=
    exists_isConstructibleSheaf_isPullback_of_isLimit (isLimitFGSubalgebraSpecCone k S) b F
  have := hasConstructibleDirectImages_of_isProper (Λ := Λ) (fgSubalgebraSpecToSpec k S (op i))
    b' F' hF' q
  have := IsConstructibleSheaf.upperStar ((fgSubalgebraSpecCone k S).π.app (op i))
    ((homologyFunctor _ q).obj ((R((b')_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F')))
  exact IsConstructibleSheaf.of_iso (upperStarHomologyRightDerivedLowerStarIsoOfIsProper H F' q ≪≫
    (homologyFunctor _ q).mapIso ((R((b)_*[ModuleCat.{u + 1} Λ])).mapIso
      ((singleFunctor _ 0).mapIso e)))

/-- **Proper direct images over a Noetherian base over a field.** Let `Λ` be a finite ring
killed by an integer invertible in the field `k`. Every proper morphism `b : Y ⟶ S` with `S`
Noetherian over `k` satisfies `𝒞(b)`: the question is local on `S`
(`AlgebraicGeometry.Etale.HasConstructibleDirectImages.of_iSup_eq_top`), and the affine case is
`AlgebraicGeometry.Etale.hasConstructibleDirectImages_of_isProper_of_isAffine`. -/
theorem hasConstructibleDirectImages_of_isProper_of_isNoetherian {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))] {Y S : Scheme.{u}} [IsNoetherian S]
    (aS : S ⟶ Spec (.of k)) (b : Y ⟶ S) [IsProper b] :
    HasConstructibleDirectImages Λ b :=
  HasConstructibleDirectImages.of_iSup_eq_top b (fun U : S.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top S) fun U ↦
      have : IsAffine U.1 := U.2
      hasConstructibleDirectImages_of_isProper_of_isAffine (U.1.ι ≫ aS) (b ∣_ U.1)

end Etale

end AlgebraicGeometry
