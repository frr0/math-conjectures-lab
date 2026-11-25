variable "github_owner" {
  description = "GitHub username or organization that owns the repository"
  type        = string
}

variable "repo_name" {
  description = "Name of the GitHub repository"
  type        = string
  default     = "math-conjectures-lab"
}

variable "repo_description" {
  description = "Short description of the GitHub repository"
  type        = string
  default     = "Automated mathematical conjecture exploration, Python verification, and Lean 4 formal proofs"
}

variable "visibility" {
  description = "Repository visibility (private or public)"
  type        = string
  default     = "private"

  validation {
    condition     = contains(["private", "public"], var.visibility)
    error_message = "visibility must be either 'private' or 'public'."
  }
}

variable "enable_rulesets" {
  description = "Enable GitHub Repository Rulesets on main (requires GitHub Pro for private repos, free for public repos)"
  type        = bool
  default     = false
}
