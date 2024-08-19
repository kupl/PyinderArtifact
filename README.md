# PyinderArtifact

```
docker build -t pyinder:1.0 .
docker run --name pyinder-container --memory-reservation 24G -it pyinder:1.0
```

### Clone Repo and Setting Configuration
```
cd ~
cd configuration
python download_repo.py
python setting_config.py
```

### Build Pyinder

```
cd ~
cd Pyinder/source
make
```


```
cd ~
python run/change_core_async.py
```

