import git
import os
import json 
from pathlib import Path
import shutil

# Git URL and commit ID for each project
with open("typebugs_repo.json", "r") as f:
    typebugs_repo = json.load(f)
with open("bugsinpy_repo.json", "r") as f:
    bugsinpy_repo = json.load(f)
with open("excepy_repo.json", "r") as f:
    excepy_repo = json.load(f)

# Directory to clone repositories into
base_dir = Path.home()

def clone_and_checkout(project, info, benchmark):
    repo_url = info['git_url']
    commit_id = info['commit_id']
    
    # repository name and directory
    repo_name = repo_url.split("/")[-1].replace(".git", "")
    repo_dir = base_dir / benchmark / repo_name

    # Clone the repository if it doesn't exist
    if not os.path.exists(repo_dir):
        print(f"Cloning {repo_name}...")
        repo = git.Repo.clone_from(repo_url, repo_dir)
    else:
        print(f"Repository {repo_name} already exists. Skipping clone.")
        repo = git.Repo(repo_dir)
    
    
    # Copy the repository to the project name
    new_repo_dir = base_dir / benchmark / project
    if not os.path.exists(new_repo_dir):
        print(f"Copying {repo_name} to {project}...")
        shutil.copytree(repo_dir, new_repo_dir)
    else:
        print(f"Project {project} already exists. Skipping copy.")

    # Checkout the commit
    print(f"Checking out commit {commit_id}...")
    repo = git.Repo(new_repo_dir)
    repo.git.checkout(commit_id, force=True)
    if project == 'salt-52624':
        repo.git.checkout("9a1ed78cca", "tests/unit/cli/test_batch.py", force=True)

def run():
    for project, info in typebugs_repo.items():
        clone_and_checkout(project, info, benchmark="typebugs")
    for project, info in bugsinpy_repo.items():
        clone_and_checkout(project, info, benchmark="bugsinpy")
    for project, info in excepy_repo.items():
        clone_and_checkout(project, info, benchmark="excepy")

if __name__ == "__main__":
    run()