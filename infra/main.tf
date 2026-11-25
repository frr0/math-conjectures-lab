terraform {
  required_version = ">= 1.6.0"

  required_providers {
    github = {
      source  = "integrations/github"
      version = "~> 6.0"
    }
  }
}

provider "github" {
  owner = var.github_owner
  # Reads GITHUB_TOKEN from the environment automatically.
}

resource "github_repository" "repo" {
  name        = var.repo_name
  description = var.repo_description
  visibility  = var.visibility

  has_issues   = true
  has_projects = false
  has_wiki     = false

  allow_merge_commit     = false
  allow_squash_merge     = true
  allow_rebase_merge     = true
  delete_branch_on_merge = true

  # Initializes the default branch (main) so branches and rulesets can be created immediately.
  auto_init = true

  topics = [
    "mathematics",
    "conjectures",
    "lean4",
    "formal-verification",
    "automated-reasoning",
  ]
}

resource "github_branch_default" "main" {
  repository = github_repository.repo.name
  branch     = "main"
  rename     = true
}

resource "github_branch" "research" {
  repository    = github_repository.repo.name
  branch        = "research"
  source_branch = github_branch_default.main.branch
}

locals {
  labels = {
    "open-target"    = { color = "0e8a16", description = "Open conjecture selected for investigation" }
    "claimed"        = { color = "fbca04", description = "Currently being worked on" }
    "counterexample" = { color = "d93f0b", description = "Disproved via verified counterexample" }
    "proved"         = { color = "1d76db", description = "Proved mathematically" }
    "lean-verified"  = { color = "5319e7", description = "Formally verified in Lean 4 without sorry" }
    "partial-result" = { color = "c2e0c6", description = "Verified partial theorem or bound" }
    "needs-audit"    = { color = "e99695", description = "Awaiting mathematical or axiom audit" }
  }
}

resource "github_issue_label" "research_labels" {
  for_each    = local.labels
  repository  = github_repository.repo.name
  name        = each.key
  color       = each.value.color
  description = each.value.description
}

# Note: Repository Rulesets on private personal repositories require GitHub Pro.
# Set enable_rulesets = true in terraform.tfvars if you have GitHub Pro or switch visibility to "public".
resource "github_repository_ruleset" "protect_main" {
  count       = var.enable_rulesets ? 1 : 0
  name        = "protect-main"
  repository  = github_repository.repo.name
  target      = "branch"
  enforcement = "active"

  conditions {
    ref_name {
      include = ["refs/heads/main"]
      exclude = []
    }
  }

  rules {
    deletion                = true
    non_fast_forward        = true
    required_linear_history = true

    pull_request {
      dismiss_stale_reviews_on_push     = true
      require_code_owner_review         = false
      required_approving_review_count   = 0
      required_review_thread_resolution = true
    }

    required_status_checks {
      strict_required_status_checks_policy = true

      required_check {
        context = "python-checks"
      }
      required_check {
        context = "lean-checks"
      }
    }
  }
}
