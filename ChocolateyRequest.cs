// 
//  Copyright (c) Microsoft Corporation. All rights reserved. 
//  Licensed under the Apache License, Version 2.0 (the "License");
//  you may not use this file except in compliance with the License.
//  You may obtain a copy of the License at
//  http://www.apache.org/licenses/LICENSE-2.0
//  
//  Unless required by applicable law or agreed to in writing, software
//  distributed under the License is distributed on an "AS IS" BASIS,
//  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//  See the License for the specific language governing permissions and
//  limitations under the License.
//  

namespace Microsoft.PackageManagement.ChocolateyPrototype {
    using System;
    using System.Collections;
    using System.Collections.Generic;
    using System.Diagnostics;
    using System.Diagnostics.CodeAnalysis;
    using System.IO;
    using System.Linq;
    using System.Management.Automation;
    using System.Reflection;
    using System.Security.Principal;
    using System.Text.RegularExpressions;
    using System.Threading.Tasks;
    using System.Xml.Linq;
    using System.Xml.XPath;
    using Common;
    using NuGet;
    using Platform;
    using Sdk;
    using Win32;
    using Constants = Sdk.Constants;
    using EnvironmentUtility = Common.EnvironmentUtility;
    using ErrorCategory = Sdk.ErrorCategory;
    using Extensions = System.Xml.XPath.Extensions;
    using PackageSource = Common.PackageSource;

    public abstract class ChocolateyRequest : Request {
        internal const string MultiplePackagesInstalledExpectedOne = "MSG:MultiplePackagesInstalledExpectedOne_package";
        private static readonly Regex _rxFastPath = new Regex(@"\$(?<source>[\w,\+,\/,=]*)\\(?<id>[\w,\+,\/,=]*)\\(?<version>[\w,\+,\/,=]*)\\(?<sources>[\w,\+,\/,=]*)");
        private static readonly Regex _rxPkgParse = new Regex(@"'(?<pkgId>\S*)\s(?<ver>.*?)'");

        internal static ImplictLazy<string> HelperModuleText = new ImplictLazy<string>(() => {
            var asm = Assembly.GetExecutingAssembly();

            var resource = asm.GetManifestResourceNames().FirstOrDefault(each => each.EndsWith("ChocolateyHelpers.psm1", StringComparison.OrdinalIgnoreCase));
            if (resource != null) {
                return StreamExtensions.ReadToEnd(asm.GetManifestResourceStream(resource));
            }
            return string.Empty;
        });

        public static ImplictLazy<bool> IsElevated = new ImplictLazy<bool>(() => {
            var id = WindowsIdentity.GetCurrent();
            var principal = new WindowsPrincipal(id);
            return principal.IsInRole(WindowsBuiltInRole.Administrator);
        });

        protected string _configurationFileLocation;
        internal ImplictLazy<bool> AllowPrereleaseVersions;
        internal ImplictLazy<bool> AllVersions;
        internal ImplictLazy<string> Contains;
        internal ImplictLazy<bool> ContinueOnFailure;
        internal ImplictLazy<bool> ExcludeVersion;
        internal ImplictLazy<string[]> FilterOnTag;
        internal ImplictLazy<bool> FindByCanonicalId;
        internal bool FoundPackageById;
        internal string[] OriginalSources;
        internal ImplictLazy<string> PackageSaveMode;
        internal ImplictLazy<bool> SkipDependencies;
        internal ImplictLazy<bool> SkipValidate;

        protected ChocolateyRequest() {
            FilterOnTag = new ImplictLazy<string[]>(() => (GetOptionValues("FilterOnTag") ?? new string[0]).ToArray());
            Contains = new ImplictLazy<string>(() => GetOptionValue("Contains"));
            SkipValidate = new ImplictLazy<bool>(() => GetOptionValue("SkipValidate").IsTrue());
            AllowPrereleaseVersions = new ImplictLazy<bool>(() => GetOptionValue("AllowPrereleaseVersions").IsTrue());
            AllVersions = new ImplictLazy<bool>(() => GetOptionValue("AllVersions").IsTrue());
            SkipDependencies = new ImplictLazy<bool>(() => GetOptionValue("SkipDependencies").IsTrue());
            ContinueOnFailure = new ImplictLazy<bool>(() => GetOptionValue("ContinueOnFailure").IsTrue());
            ExcludeVersion = new ImplictLazy<bool>(() => GetOptionValue("ExcludeVersion").IsTrue());
            FindByCanonicalId = new ImplictLazy<bool>(() => GetOptionValue("FindByCanonicalId").IsTrue());
            PackageSaveMode = new ImplictLazy<string>(() => {
                var sm = GetOptionValue("PackageSaveMode");
                if (string.IsNullOrEmpty(sm)) {
                    sm = "nupkg";
                }
                return sm;
            });
        }

        internal IEnumerable<PackageSource> SelectedSources {
            get {
                var sources = (OriginalSources ?? Enumerable.Empty<string>()).Union(PackageSources ?? Enumerable.Empty<string>()).ToArray();
                var pkgSources = RegisteredPackageSources;

                if (sources.Length == 0) {
                    // return them all.
                    foreach (var src in pkgSources.Values) {
                        yield return src;
                    }
                    yield break;
                }

                // we don't want to return duplicate sources
                HashSet<string> usedPkgSourceKeys = new HashSet<string>();

                // otherwise, return package sources that match the items given
                foreach (var src in sources) {
                    // check to see if we have a source with either that name
                    // or that URI first.
                    if (pkgSources.ContainsKey(src)) {
                        if (!usedPkgSourceKeys.Contains(src)) {
                            usedPkgSourceKeys.Add(src);
                            yield return pkgSources[src];
                            continue;
                        }
                    }

                    var srcLoc = src;
                    var found = false;
                    foreach (var byLoc in pkgSources.Where(each => each.Value.Location == srcLoc)) {
                        if (!usedPkgSourceKeys.Contains(byLoc.Key)) {
                            usedPkgSourceKeys.Add(byLoc.Key);
                            yield return byLoc.Value;
                            found = true;
                        }
                    }
                    if (found) {
                        continue;
                    }

                    // doesn't look like we have this as a source.
                    if (Uri.IsWellFormedUriString(src, UriKind.Absolute)) {
                        // we have been passed in an URI
                        var srcUri = new Uri(src);
                        if (SupportedSchemes.Contains(srcUri.Scheme.ToLower())) {
                            // it's one of our supported uri types.
                            var isValidated = false;

                            if (!SkipValidate) {
                                isValidated = ValidateSourceUri(srcUri);
                            }

                            if (SkipValidate || isValidated) {
                                yield return new PackageSource {
                                    Location = srcUri.ToString(),
                                    Name = srcUri.ToString(),
                                    Trusted = false,
                                    IsRegistered = false,
                                    IsValidated = isValidated,
                                };
                                continue;
                            }
                            Error(ErrorCategory.InvalidArgument, src, Constants.Messages.SourceLocationNotValid, src);
                            Warning(Constants.Messages.UnableToResolveSource, src);
                            continue;
                        }

                        // hmm. not a valid location?
                        Error(ErrorCategory.InvalidArgument, src, Constants.Messages.UriSchemeNotSupported, src);
                        Warning(Constants.Messages.UnableToResolveSource, src);
                        continue;
                    }

                    // is it a file path?
                    if (Directory.Exists(src)) {
                        yield return new PackageSource {
                            Location = src,
                            Name = src,
                            Trusted = true,
                            IsRegistered = false,
                            IsValidated = true,
                        };
                    } else {
                        // hmm. not a valid location?
                        Warning(Constants.Messages.UnableToResolveSource, src);
                    }
                }
            }
        }

        internal static string NuGetExePath {
            get {
                return typeof (AggregateRepository).Assembly.Location;
            }
        }

        internal IEnumerable<string> SupportedSchemes {
            get {
                return ChocolateyProvider.Features[Constants.Features.SupportedSchemes];
            }
        }

        public string PackageProviderName {
            get {
                return ChocolateyProvider.ProviderName;
            }
        }

        internal bool ForceX86 {
            [SuppressMessage("Microsoft.Performance", "CA1811:AvoidUncalledPrivateCode", Justification = "Required.")]
            get {
                return GetOptionValue("ForceX86").IsTrue();
            }
        }

        internal string Destination {
            get {
                return PackageInstallationPath;
            }
        }

        internal IDictionary<string, PackageSource> RegisteredPackageSources {
            get {
                try {
                    return Extensions.XPathSelectElements(Config, "/chocolatey/sources/source")
                        .Where(each => each.Attribute("id") != null && each.Attribute("value") != null)
                        .ToDictionaryNicely(each => each.Attribute("id").Value, each => new PackageSource {
                            Name = each.Attribute("id").Value,
                            Location = each.Attribute("value").Value,
                            Trusted = each.Attributes("trusted").Any() && each.Attribute("trusted").Value.IsTrue(),
                            IsRegistered = true,
                            IsValidated = each.Attributes("validated").Any() && each.Attribute("validated").Value.IsTrue(),
                        }, StringComparer.OrdinalIgnoreCase);
                } catch (Exception e) {
                    e.Dump(this);
                }
                return new Dictionary<string, PackageSource>(StringComparer.OrdinalIgnoreCase) {
                    {
                        "chocolatey", new PackageSource {
                            Name = "chocolatey",
                            Location = "http://chocolatey.org/api/v2/",
                            Trusted = false,
                            IsRegistered = false,
                            IsValidated = true,
                        }
                    }
                };
            }
        }

        internal XDocument Config {
            get {
                try {
                    var doc = XDocument.Load((string)ChocolateyConfigPath);
                    if (doc.Root != null && doc.Root.Name == "chocolatey") {
                        return doc;
                    }

                    // doc root isn't right. make a new one!
                } catch {
                    // bad doc
                }
                return XDocument.Load(new MemoryStream(@"<?xml version=""1.0""?>
<chocolatey>
    <useNuGetForSources>false</useNuGetForSources>
    <sources>
        <source id=""chocolatey"" value=""http://chocolatey.org/api/v2/"" />
    </sources>
</chocolatey>
".ToByteArray()));
            }
            set {
                Verbose("Saving Chocolatey Config {0}", ChocolateyConfigPath);

                if (value == null) {
                    return;
                }

                CreateFolder(Path.GetDirectoryName(ChocolateyConfigPath));
                value.Save((string)ChocolateyConfigPath);
            }
        }

        internal string PackageInstallationPath {
            get {
                var path = Path.Combine(RootInstallationPath, "lib");
                if (!Directory.Exists(path)) {
                    CreateFolder(path);
                }
                return path;
            }
        }

        internal string PackageExePath {
            get {
                var path = Path.Combine(RootInstallationPath, "bin");
                if (!Directory.Exists(path)) {
                    CreateFolder(path);
                }
                return Path.Combine(RootInstallationPath, "bin");
            }
        }

        protected string ConfigurationFileLocation {
            get {
                return ChocolateyConfigPath;
            }
        }

        private bool LocationCloseEnoughMatch(string givenLocation, string knownLocation) {
            if (givenLocation.Equals(knownLocation, StringComparison.OrdinalIgnoreCase)) {
                return true;
            }

            // make trailing slashes consistent
            if (givenLocation.TrimEnd('/').Equals(knownLocation.TrimEnd('/'), StringComparison.OrdinalIgnoreCase)) {
                return true;
            }

            // and trailing backslashes
            if (givenLocation.TrimEnd('\\').Equals(knownLocation.TrimEnd('\\'), StringComparison.OrdinalIgnoreCase)) {
                return true;
            }
            return false;
        }

        internal PackageSource FindRegisteredSource(string name) {
            var srcs = RegisteredPackageSources;
            if (srcs.ContainsKey(name)) {
                return srcs[name];
            }

            var src = srcs.Values.FirstOrDefault(each => LocationCloseEnoughMatch(name, each.Location));
            if (src != null) {
                return src;
            }

            return null;
        }

        internal bool ValidateSourceLocation(string location) {
            if (Uri.IsWellFormedUriString(location, UriKind.Absolute)) {
                return ValidateSourceUri(new Uri(location));
            }
            try {
                if (Directory.Exists(location) || File.Exists(location)) {
                    return true;
                }
            } catch {
            }
            return false;
        }

        private bool ValidateSourceUri(Uri srcUri) {
            if (!SupportedSchemes.Contains(srcUri.Scheme.ToLowerInvariant())) {
                return false;
            }

            if (srcUri.IsFile) {
                var path = srcUri.ToString().CanonicalizePath(false);

                if (Directory.Exists(path)) {
                    return true;
                }
                return false;
            }

            // todo: do a get on the uri and see if it responds.
            try {
                var repo = PackageRepositoryFactory.Default.CreateRepository(srcUri.ToString());
                var drepo = repo as DataServicePackageRepository;
                if (drepo != null) {
                    drepo.FindPackagesById("xx");
                }
                return true;
            } catch {
                // nope.
            }

            return false;
        }

        internal PackageSource ResolvePackageSource(string nameOrLocation) {
            var source = FindRegisteredSource(nameOrLocation);
            if (source != null) {
                return source;
            }

            try {
                // is the given value a filename?
                if (File.Exists(nameOrLocation)) {
                    return new PackageSource() {
                        IsRegistered = false,
                        IsValidated = true,
                        Location = nameOrLocation,
                        Name = nameOrLocation,
                        Trusted = true,
                    };
                }
            } catch {
            }

            try {
                // is the given value a directory?
                if (Directory.Exists(nameOrLocation)) {
                    return new PackageSource() {
                        IsRegistered = false,
                        IsValidated = true,
                        Location = nameOrLocation,
                        Name = nameOrLocation,
                        Trusted = true,
                    };
                }
            } catch {
            }

            if (Uri.IsWellFormedUriString(nameOrLocation, UriKind.Absolute)) {
                var uri = new Uri(nameOrLocation, UriKind.Absolute);
                if (!SupportedSchemes.Contains(uri.Scheme.ToLowerInvariant())) {
                    Error(ErrorCategory.InvalidArgument, uri.ToString(), Constants.Messages.UriSchemeNotSupported, uri);
                    return null;
                }

                // this is an URI, and it looks like one type that we support
                if (SkipValidate || ValidateSourceUri(uri)) {
                    return new PackageSource {
                        IsRegistered = false,
                        IsValidated = !SkipValidate,
                        Location = nameOrLocation,
                        Name = nameOrLocation,
                        Trusted = false,
                    };
                }
            }

            Error(ErrorCategory.InvalidArgument, nameOrLocation, Constants.Messages.UnableToResolveSource, nameOrLocation);
            return null;
        }

        internal IEnumerable<IPackage> FilterOnVersion(IEnumerable<IPackage> pkgs, string requiredVersion, string minimumVersion, string maximumVersion) {
            if (!String.IsNullOrEmpty(requiredVersion)) {
                pkgs = pkgs.Where(each => each.Version == new SemanticVersion(requiredVersion));
            } else {
                if (!String.IsNullOrEmpty(minimumVersion)) {
                    pkgs = pkgs.Where(each => each.Version >= new SemanticVersion(minimumVersion));
                }

                if (!String.IsNullOrEmpty(maximumVersion)) {
                    pkgs = pkgs.Where(each => each.Version <= new SemanticVersion(maximumVersion));
                }
            }
            return pkgs;
        }

        internal IEnumerable<PackageItem> FilterOnVersion(IEnumerable<PackageItem> pkgs, string requiredVersion, string minimumVersion, string maximumVersion) {
            if (!String.IsNullOrEmpty(requiredVersion)) {
                pkgs = pkgs.Where(each => new SemanticVersion(each.Version) == new SemanticVersion(requiredVersion));
            } else {
                if (!String.IsNullOrEmpty(minimumVersion)) {
                    pkgs = pkgs.Where(each => new SemanticVersion(each.Version) >= new SemanticVersion(minimumVersion));
                }

                if (!String.IsNullOrEmpty(maximumVersion)) {
                    pkgs = pkgs.Where(each => new SemanticVersion(each.Version) <= new SemanticVersion(maximumVersion));
                }
            }
            return pkgs;
        }

        internal string MakeFastPath(PackageSource source, string id, string version) {
            return String.Format(@"${0}\{1}\{2}\{3}", source.Serialized, id.ToBase64(), version.ToBase64(), (Sources ?? new string[0]).Select(each => each.ToBase64()).SafeAggregate((current, each) => current + "|" + each));
        }

        public bool TryParseFastPath(string fastPath, out string source, out string id, out string version, out string[] sources) {
            var match = _rxFastPath.Match(fastPath);
            source = match.Success ? match.Groups["source"].Value.FromBase64() : null;
            id = match.Success ? match.Groups["id"].Value.FromBase64() : null;
            version = match.Success ? match.Groups["version"].Value.FromBase64() : null;
            var srcs = match.Success ? match.Groups["sources"].Value : string.Empty;
            sources = srcs.Split('|').Select(each => each.FromBase64()).Where(each => !string.IsNullOrWhiteSpace(each)).ToArray();
            return match.Success;
        }

        internal bool YieldPackage(PackageItem pkg, string searchKey) {
            try {
                if (YieldSoftwareIdentity(pkg.FastPath, pkg.Package.Id, pkg.Package.Version.ToString(), "semver", pkg.Package.Summary, pkg.PackageSource.Name, searchKey, pkg.FullPath, pkg.PackageFilename) != null) {
                    // iterate thru the dependencies and add them to the software identity.
                    foreach (var depSet in pkg.Package.DependencySets) {
                        foreach (var dep in depSet.Dependencies) {
                            var dependency = AddDependency(PackageProviderName, dep.Id, dep.VersionSpec == null ? null : dep.VersionSpec.ToString(), null, null);
                            // todo: determine if we can generate an appropriate "appliesTo" for the package.

                            if (IsCanceled) {
                                return false;
                            }
                        }
                    }

                    if (AddMetadata(pkg.FastPath, "copyright", pkg.Package.Copyright) == null) {
                        return false;
                    }
                    if (AddMetadata(pkg.FastPath, "description", pkg.Package.Description) == null) {
                        return false;
                    }
                    if (AddMetadata(pkg.FastPath, "language", pkg.Package.Language) == null) {
                        return false;
                    }
                    if (AddMetadata(pkg.FastPath, "releaseNotes", pkg.Package.ReleaseNotes) == null) {
                        return false;
                    }
                    if (pkg.Package.Published != null) {
                        // published time.
                        if (AddMetadata(pkg.FastPath, "published", pkg.Package.Published.ToString()) == null) {
                            return false;
                        }
                    }
                    if (AddMetadata(pkg.FastPath, "tags", pkg.Package.Tags) == null) {
                        return false;
                    }
                    if (AddMetadata(pkg.FastPath, "title", pkg.Package.Title) == null) {
                        return false;
                    }
                    if (AddMetadata(pkg.FastPath, "developmentDependency", pkg.Package.DevelopmentDependency.ToString()) == null) {
                        return false;
                    }
                    if (AddMetadata(pkg.FastPath, "FromTrustedSource", pkg.PackageSource.Trusted.ToString()) == null) {
                        return false;
                    }
                    if (pkg.Package.LicenseUrl != null && !String.IsNullOrEmpty(pkg.Package.LicenseUrl.ToString())) {
                        if (AddLink(pkg.Package.LicenseUrl, "license", null, null, null, null, null) == null) {
                            return false;
                        }
                    }
                    if (pkg.Package.ProjectUrl != null && !String.IsNullOrEmpty(pkg.Package.ProjectUrl.ToString())) {
                        if (AddLink(pkg.Package.ProjectUrl, "project", null, null, null, null, null) == null) {
                            return false;
                        }
                    }
                    if (pkg.Package.ReportAbuseUrl != null && !String.IsNullOrEmpty(pkg.Package.ReportAbuseUrl.ToString())) {
                        if (AddLink(pkg.Package.ReportAbuseUrl, "abuse", null, null, null, null, null) == null) {
                            return false;
                        }
                    }
                    if (pkg.Package.IconUrl != null && !String.IsNullOrEmpty(pkg.Package.IconUrl.ToString())) {
                        if (AddLink(pkg.Package.IconUrl, "icon", null, null, null, null, null) == null) {
                            return false;
                        }
                    }
                    if (pkg.Package.Authors.Any(author => AddEntity(author.Trim(), author.Trim(), "author", null) == null)) {
                        return false;
                    }

                    if (pkg.Package.Owners.Any(owner => AddEntity(owner.Trim(), owner.Trim(), "owner", null) == null)) {
                        return false;
                    }
                } else {
                    return false;
                }
            } catch (Exception e) {
                e.Dump(this);
                return false;
            }
            return true;
        }

        internal bool YieldPackages(IEnumerable<PackageItem> packageReferences, string searchKey) {
            var foundPackage = false;
            if (packageReferences == null) {
                return false;
            }
            Debug("Iterating");

            foreach (var pkg in packageReferences) {
                foundPackage = true;
                try {
                    Debug("Yielding");
                    if (!YieldPackage(pkg, searchKey)) {
                        break;
                    }
                } catch (Exception e) {
                    e.Dump(this);
                    return false;
                }
            }

            Debug("Done Iterating");
            return foundPackage;
        }

        internal IEnumerable<PackageItem> GetPackageById(PackageSource source, string name, string requiredVersion = null, string minimumVersion = null, string maximumVersion = null, bool allowUnlisted = false) {
            try {
                if (!string.IsNullOrWhiteSpace(requiredVersion) && requiredVersion.IndexOfAny(new char[] {'[', ']', '(', ')'}) > -1) {
                    IVersionSpec versionSpec;
                    if (VersionUtility.TryParseVersionSpec(requiredVersion, out versionSpec)) {
                        // we've got a IVersionSpec -- we can search with that.

                        // plus, if we're handling a version range like this, we don't want to do any tags or filters.
                        // so just return this set simply.
                        return source.Repository.FindPackages(name, versionSpec, AllowPrereleaseVersions, allowUnlisted).Select(pkg => new PackageItem {
                            Package = pkg,
                            PackageSource = source,
                            FastPath = MakeFastPath(source, pkg.Id, pkg.Version.ToString())
                        });
                    }
                }

                // otherwise fall back to traditional behavior 
                // search by package id without version
                // then apply whatever filters are required.
                IEnumerable<IPackage> pkgs = source.Repository.FindPackagesById(name).ReEnumerable();
                if (pkgs.Any()) {
                    // this meas that we actually found an exact package name match, which is important
                    // so we can not do a search later.
                    FoundPackageById = true;

                    if (!AllVersions && (String.IsNullOrEmpty(requiredVersion) && String.IsNullOrEmpty(minimumVersion) && String.IsNullOrEmpty(maximumVersion))) {
                        pkgs = from p in pkgs where p.IsLatestVersion select p;
                    }

                    pkgs = FilterOnContains(pkgs);
                    pkgs = FilterOnTags(pkgs);

                    return FilterOnVersion(pkgs, requiredVersion, minimumVersion, maximumVersion)
                        .Select(pkg => new PackageItem {
                            Package = pkg,
                            PackageSource = source,
                            FastPath = MakeFastPath(source, pkg.Id, pkg.Version.ToString())
                        });
                }
            } catch (Exception e) {
                e.Dump(this);
            }
            return Enumerable.Empty<PackageItem>();
        }

        internal IEnumerable<PackageItem> GetPackageById(string name, string requiredVersion = null, string minimumVersion = null, string maximumVersion = null, bool allowUnlisted = false) {
            if (String.IsNullOrEmpty(name)) {
                return Enumerable.Empty<PackageItem>();
            }
            return SelectedSources.AsParallel().WithMergeOptions(ParallelMergeOptions.NotBuffered).SelectMany(source => GetPackageById(source, name, requiredVersion, minimumVersion, maximumVersion, allowUnlisted));
        }

        internal IEnumerable<IPackage> FilterOnName(IEnumerable<IPackage> pkgs, string name) {
            return pkgs.Where(each => each.Id != null && each.Id.IndexOf(name, StringComparison.OrdinalIgnoreCase) > -1);
        }

        internal IEnumerable<IPackage> FilterOnTags(IEnumerable<IPackage> pkgs) {
            if (FilterOnTag == null || FilterOnTag.Value.Length == 0) {
                return pkgs;
            }
            return pkgs.Where(each => each.Tags != null && FilterOnTag.Value.Any(tag => each.Tags.IndexOf(tag, StringComparison.OrdinalIgnoreCase) > -1));
        }

        internal IEnumerable<IPackage> FilterOnContains(IEnumerable<IPackage> pkgs) {
            if (string.IsNullOrEmpty(Contains)) {
                return pkgs;
            }
            return pkgs.Where(each => (each.Description != null && each.Description.IndexOf(Contains, StringComparison.OrdinalIgnoreCase) > -1) || (each.Id != null && each.Id.IndexOf(Contains, StringComparison.OrdinalIgnoreCase) > -1));
        }

        internal PackageItem GetPackageByFilePath(string filePath) {
            // todo: currently requires nupkg file in place.

            if (PackageHelper.IsPackageFile(filePath)) {
                var package = new ZipPackage(filePath);
                var source = ResolvePackageSource(filePath);

                return new PackageItem {
                    FastPath = MakeFastPath(source, package.Id, package.Version.ToString()),
                    PackageSource = source,
                    Package = package,
                    IsPackageFile = true,
                    FullPath = filePath,
                };
            }
            return null;
        }

        internal PackageItem GetPackageByFastpath(string fastPath) {
            string sourceLocation;
            string id;
            string version;
            string[] sources;

            if (TryParseFastPath(fastPath, out sourceLocation, out id, out version, out sources)) {
                var source = ResolvePackageSource(sourceLocation);

                if (source.IsSourceAFile) {
                    return GetPackageByFilePath(sourceLocation);
                }

                var pkg = source.Repository.FindPackage(id, new SemanticVersion(version));

                if (pkg != null) {
                    return new PackageItem {
                        FastPath = fastPath,
                        PackageSource = source,
                        Package = pkg,
                        Sources = sources
                    };
                }
            }
            return null;
        }

        internal IEnumerable<PackageItem> SearchForPackages(string name, string requiredVersion, string minimumVersion, string maximumVersion) {
            return SelectedSources.AsParallel().WithMergeOptions(ParallelMergeOptions.NotBuffered).SelectMany(source => SearchSourceForPackages(source, name, requiredVersion, minimumVersion, maximumVersion));
        }

        internal IEnumerable<PackageItem> FindPackageByNameFirst(PackageSource source, string name, string requiredVersion, string minimumVersion, string maximumVersion) {
            var package = GetPackageById(source, name, requiredVersion, minimumVersion, maximumVersion).ToArray();
            return package.Length > 0 ? package : SearchSourceForPackages(source, name, requiredVersion, minimumVersion, maximumVersion);
        }

        private IEnumerable<PackageItem> SearchSourceForPackages(PackageSource source, string name, string requiredVersion, string minimumVersion, string maximumVersion) {
            try {
                if (!String.IsNullOrEmpty(name) && WildcardPattern.ContainsWildcardCharacters(name)) {
                    // NuGet does not support PowerShell/POSIX style wildcards and supports only '*' in searchTerm with NuGet.exe
                    // Replace the range from '[' - to ']' with * and ? with * then wildcard pattern is applied on the results from NuGet.exe
                    var tempName = name;
                    var squareBracketPattern = Regex.Escape("[") + "(.*?)]";
                    foreach (Match match in Regex.Matches(tempName, squareBracketPattern)) {
                        tempName = tempName.Replace(match.Value, "*");
                    }
                    var searchTerm = tempName.Replace("?", "*");

                    // Wildcard pattern matching configuration.
                    const WildcardOptions wildcardOptions = WildcardOptions.CultureInvariant | WildcardOptions.IgnoreCase;
                    var wildcardPattern = new WildcardPattern(searchTerm, wildcardOptions);

                    IEnumerable<string> packageIds = null;
                    using (var p = AsyncProcess.Start(NuGetExePath, String.Format(@"list ""{0}"" -Source ""{1}"" ", searchTerm, source.Location))) {
                        packageIds = p.StandardOutput.Where(each => !String.IsNullOrEmpty(each)).Select(l => {
                            Debug("NuGet: {0}", l);
                            if (l.Contains("No packages found.")) {
                                return null;
                            }
                            // ComicRack 0.9.162
                            var packageDetails = l.Split();

                            if (wildcardPattern.IsMatch(packageDetails[0])) {
                                return packageDetails[0];
                            }
                            return null;
                        }).Where(each => each != null).ToArray();

                        foreach (var l in p.StandardError.Where(l => !String.IsNullOrEmpty(l))) {
                            Warning("NuGet: {0}", l);
                        }
                    }
                    return packageIds.SelectMany(packageId => GetPackageById(source, packageId, requiredVersion, minimumVersion, maximumVersion));
                }
            } catch (Exception e) {
                e.Dump(this);
                return Enumerable.Empty<PackageItem>();
            }

            try {
                var criteria = Contains.Value;
                if (String.IsNullOrEmpty(criteria)) {
                    criteria = name;
                }

                if (FilterOnTag != null) {
                    criteria = FilterOnTag.Value.Where(tag => !string.IsNullOrEmpty(tag)).Aggregate(criteria, (current, tag) => current + " tag:" + tag);
                }
                Debug("Searching repository '{0}' for '{1}'", source.Repository.Source, criteria);
                var src = source.Repository;
                /*
                IQueryable<IPackage> packages;
                if (src is IServiceBasedRepository) {
                    packages = (src as IServiceBasedRepository).Search(criteria, new string[0], AllowPrereleaseVersions);
                } else {
                    packages = src.Search(criteria, AllowPrereleaseVersions);
                }
                */

                var packages = src.Search(criteria, AllowPrereleaseVersions);

                /*
                foreach (var p in pp) {
                    Console.WriteLine(p.GetFullName());
                }
                */

                // packages = packages.OrderBy(p => p.Id);

                // query filtering:
                if (!AllVersions && (String.IsNullOrEmpty(requiredVersion) && String.IsNullOrEmpty(minimumVersion) && String.IsNullOrEmpty(maximumVersion))) {
                    packages = packages.FindLatestVersion();
                }

                IEnumerable<IPackage> pkgs = new PackagesEnumerable(packages);

                // if they passed a name, restrict the search things that actually contain the name in the FullName.
                if (!String.IsNullOrEmpty(name)) {
                    pkgs = FilterOnName(pkgs, name);
                }

                pkgs = FilterOnTags(pkgs);

                pkgs = FilterOnContains(pkgs);

                return FilterOnVersion(pkgs, requiredVersion, minimumVersion, maximumVersion)
                    .Select(pkg => new PackageItem {
                        Package = pkg,
                        PackageSource = source,
                        FastPath = MakeFastPath(source, pkg.Id, pkg.Version.ToString())
                    });
            } catch (Exception e) {
                e.Dump(this);
                return Enumerable.Empty<PackageItem>();
            }
        }

        public bool IsPackageInstalled(string name, string version) {
#if find_installed_packages_with_nuspec

            var nuspecs = from pkgFile in Directory.EnumerateFileSystemEntries(Destination, "*.nuspec", SearchOption.AllDirectories) select pkgFile ;

            foreach (var n in nuspecs) {
                // uh, do we have to parse these?
                // hmmm.
            }

            // or we could search in this folder for a directory with or without the version
            // then examine the contents.
            // hmmm. I'd rather let nuget do that if I can, it's better at it.

#endif
            return (from pkgFile in Directory.EnumerateFileSystemEntries(Destination, "*.nupkg", SearchOption.AllDirectories)
                where PackageHelper.IsPackageFile(pkgFile)
                select new ZipPackage(pkgFile))
                .Any(pkg => pkg.Id.Equals(name, StringComparison.OrdinalIgnoreCase) && pkg.Version.ToString().Equals(version, StringComparison.OrdinalIgnoreCase));
        }

        internal IEnumerable<PackageItem> GetUninstalledPackageDependencies(PackageItem packageItem) {
            foreach (var depSet in packageItem.Package.DependencySets) {
                foreach (var dep in depSet.Dependencies) {
                    // get all the packages that match this dependency
                    var depRefs = dep.VersionSpec == null ? GetPackageById(dep.Id).ToArray() : GetPackageByIdAndVersionSpec(dep.Id, dep.VersionSpec, true).ToArray();

                    if (depRefs.Length == 0) {
                        Error(ErrorCategory.ObjectNotFound, packageItem.GetCanonicalId(this), Constants.Messages.DependencyResolutionError, ProviderServices.GetCanonicalPackageId(PackageProviderName, dep.Id, ((object)dep.VersionSpec ?? "").ToString(), null));
                        throw new Exception("failed");
                    }

                    if (depRefs.Any(each => IsPackageInstalled(each.Id, each.Version))) {
                        // we have a compatible version installed.
                        continue;
                    }

                    yield return depRefs[0];

                    // it's not installed. return this as a needed package, but first, get it's dependencies.
                    foreach (var nestedDep in GetUninstalledPackageDependencies(depRefs[0])) {
                        yield return nestedDep;
                    }
                }
            }
        }

        private PackageItem ParseOutputFull(PackageSource source, string packageId, string version, string line) {
            var match = _rxPkgParse.Match(line);
            if (match.Success) {
                var pkg = new PackageItem {
                    Id = match.Groups["pkgId"].Value,
                    Version = match.Groups["ver"].Value,
                };

                // if this was the package we started with, we can assume a bit more info,
                if (pkg.Id == packageId && pkg.Version == version) {
                    pkg.PackageSource = source;
                }
                pkg.FullPath = Path.Combine(Destination, ExcludeVersion ? pkg.Id : pkg.FullName);
                return pkg;
            }
            return null;
        }

        internal InstallResult NuGetInstall(PackageItem item) {
            var result = new InstallResult();

            using (
                var p = AsyncProcess.Start(NuGetExePath,
                    String.Format(@"install ""{0}"" -Version ""{1}"" -Source ""{2}"" -PackageSaveMode ""{4}""  -OutputDirectory ""{3}"" -Verbosity detailed {5}", item.Id, item.Version, item.PackageSource.Location, Destination, PackageSaveMode.Value,
                        ExcludeVersion ? "-ExcludeVersion" : ""))
                ) {
                foreach (var l in p.StandardOutput) {
                    if (String.IsNullOrEmpty(l)) {
                        continue;
                    }

                    Verbose("NuGet: {0}", l);
                    // Successfully installed 'ComicRack 0.9.162'.
                    if (l.Contains("Successfully installed")) {
                        result.GetOrAdd(InstallStatus.Successful, () => new List<PackageItem>()).Add(ParseOutputFull(item.PackageSource, item.Id, item.Version, l));
                        continue;
                    }
                    ;

                    if (l.Contains("already installed")) {
                        result.GetOrAdd(InstallStatus.AlreadyPresent, () => new List<PackageItem>()).Add(ParseOutputFull(item.PackageSource, item.Id, item.Version, l));
                        continue;
                    }

                    if (l.Contains("not installed")) {
                        result.GetOrAdd(InstallStatus.Failed, () => new List<PackageItem>()).Add(ParseOutputFull(item.PackageSource, item.Id, item.Version, l));
                        continue;
                    }
                }

                foreach (var l in p.StandardError.Where(l => !String.IsNullOrEmpty(l))) {
                    Warning("NuGet: {0}", l);
                }

                // if anything failed, this is a failure.
                // if we have a success message (and no failure), we'll count this as a success.
                result.Status = result.ContainsKey(InstallStatus.Failed) ? InstallStatus.Failed : result.ContainsKey(InstallStatus.Successful) ? InstallStatus.Successful : InstallStatus.AlreadyPresent;

                return result;
            }
        }

        internal IEnumerable<PackageItem> GetPackageByIdAndVersionSpec(string name, IVersionSpec versionSpec, bool allowUnlisted = false) {
            if (String.IsNullOrEmpty(name)) {
                return Enumerable.Empty<PackageItem>();
            }

            return SelectedSources.AsParallel().WithMergeOptions(ParallelMergeOptions.NotBuffered).SelectMany(source => {
                try {
                    var pkgs = source.Repository.FindPackages(name, versionSpec, AllowPrereleaseVersions, allowUnlisted);

                    /*
                // necessary?
                pkgs = from p in pkgs where p.IsLatestVersion select p;
                */

                    var pkgs2 = pkgs.ToArray();

                    return pkgs2.Select(pkg => new PackageItem {
                        Package = pkg,
                        PackageSource = source,
                        FastPath = MakeFastPath(source, pkg.Id, pkg.Version.ToString())
                    });
                } catch {
                    return new PackageItem[0];
                }
            }).OrderByDescending(each => each.Package.Version);
        }

        internal bool PostInstall(PackageItem packageItem) {
            // run the install script
            var pkgPath = packageItem.FullPath;
            var scripts = Directory.EnumerateFiles(pkgPath, "chocolateyInstall.ps1", SearchOption.AllDirectories);
            var script = scripts.FirstOrDefault();
            if (script != null) {
                try {
                    Environment.SetEnvironmentVariable("chocolateyPackageFolder", pkgPath);
                    Environment.SetEnvironmentVariable("chocolateyInstallArguments", "");
                    Environment.SetEnvironmentVariable("chocolateyInstallOverride", "");

                    InvokeChocolateyScript(script, pkgPath);
                } catch (Exception e) {
                    e.Dump(this);
                    return false;
                } finally {
                    Environment.SetEnvironmentVariable("chocolateyPackageFolder", null);
                    Environment.SetEnvironmentVariable("chocolateyInstallArguments", null);
                    Environment.SetEnvironmentVariable("chocolateyInstallOverride", null);
                }
            }

            // Now handle 'bins'
            return GenerateBins(pkgPath);
        }

        internal bool PostUninstall(PackageItem packageItem) {
            // run the uninstall script
            return true;
        }

        internal bool PreInstall(PackageItem packageItem) {
            // run the install script
            return true;
        }

        internal bool PreUninstall(PackageItem packageItem) {
            // run the uninstall script
            return true;
        }

        internal bool InstallSinglePackage(PackageItem packageItem) {
            // Get NuGet to install the Package
            PreInstall(packageItem);
            var results = NuGetInstall(packageItem);

            if (results.Status == InstallStatus.Successful) {
                foreach (var installedPackage in results[InstallStatus.Successful]) {
                    if (IsCanceled) {
                        // the caller has expressed that they are cancelling the install.
                        Verbose("Package installation cancelled");
                        // todo: we should probablty uninstall this package unless the user said leave broken stuff behind
                        return false;
                    }

                    // run any extra steps
                    if (!PostInstall(installedPackage)) {
                        // package failed installation. uninstall it.
                        UninstallPackage(installedPackage);

                        return false;
                    }

                    YieldPackage(packageItem, packageItem.PackageSource.Name);
                    // yay!
                }
                return true;
            }

            if (results.Status == InstallStatus.AlreadyPresent) {
                // hmm Weird.
                Verbose("Skipped Package '{0} v{1}' already installed", packageItem.Id, packageItem.Version);
                return true;
            }

            Error(ErrorCategory.InvalidResult, packageItem.GetCanonicalId(this), MultiplePackagesInstalledExpectedOne, packageItem.GetCanonicalId(this));

            return false;
        }

        public bool IsReady(bool b) {
            return true;
        }

        internal bool UninstallPackage(PackageItem pkg) {
            var dir = pkg.InstalledDirectory;

            if (!String.IsNullOrEmpty(dir) && Directory.Exists(dir)) {
                if (PreUninstall(pkg)) {
                    DeleteFolder(pkg.InstalledDirectory);
                }
                var result = PostUninstall(pkg);
                YieldPackage(pkg, pkg.Id);
                return result;
            }
            return true;
        }

        public void AddPinnedItemToTaskbar(string item) {
            if (!IsCanceled) {
                Debug("Calling 'ProviderService::AddPinnedItemToTaskbar'");
                ShellApplication.Pin(item);
            }
        }

        public void RemovePinnedItemFromTaskbar(string item) {
            if (!IsCanceled) {
                Debug("Calling 'ProviderService::RemovePinnedItemFromTaskbar'");
                ShellApplication.Unpin(item);
            }
        }

        public void CreateShortcutLink(string linkPath, string targetPath, string description, string workingDirectory, string arguments) {
            if (!IsCanceled) {
                Debug("Calling 'ProviderService::CreateShortcutLink'");

                if (File.Exists(linkPath)) {
                    Verbose("Creating Shortcut '{0}' => '{1}'", linkPath, targetPath);
                    ShellLink.CreateShortcut(linkPath, targetPath, description, workingDirectory, arguments);
                }
                Error(ErrorCategory.InvalidData, targetPath, Constants.Messages.UnableToCreateShortcutTargetDoesNotExist, targetPath);
            }
        }

        public void CopyFile(string sourcePath, string destinationPath) {
            if (!IsCanceled) {
                Debug("Calling 'ProviderService::CopyFile'");
                if (sourcePath == null) {
                    throw new ArgumentNullException("sourcePath");
                }
                if (destinationPath == null) {
                    throw new ArgumentNullException("destinationPath");
                }
                if (File.Exists(destinationPath)) {
                    destinationPath.TryHardToDelete();
                    if (File.Exists(destinationPath)) {
                        Error(ErrorCategory.OpenError, destinationPath, Constants.Messages.UnableToOverwriteExistingFile, destinationPath);
                    }
                }
                File.Copy(sourcePath, destinationPath);
                if (!File.Exists(destinationPath)) {
                    Error(ErrorCategory.InvalidResult, destinationPath, Constants.Messages.UnableToCopyFileTo, destinationPath);
                }
            }
        }

        public void Delete(string path) {
            if (!IsCanceled) {
                Debug("Calling 'ProviderService::Delete'");
                if (String.IsNullOrWhiteSpace(path)) {
                    return;
                }

                path.TryHardToDelete();
            }
        }

        public void DeleteFolder(string folder) {
            if (!IsCanceled) {
                Debug("Calling 'ProviderService::DeleteFolder' {0}".format(folder));
                if (String.IsNullOrWhiteSpace(folder)) {
                    return;
                }
                if (Directory.Exists(folder)) {
                    folder.TryHardToDelete();
                }
            }
        }

        public void CreateFolder(string folder) {
            if (!IsCanceled) {
                Debug("Calling 'ProviderService::CreateFolder'");

                if (!Directory.Exists(folder)) {
                    try {
                        Directory.CreateDirectory(folder);
                        Verbose("CreateFolder Success {0}", folder);
                        return;
                    } catch (Exception e) {
                        Error(ErrorCategory.InvalidResult, folder, Constants.Messages.CreatefolderFailed, folder, e.Message);
                        return;
                    }
                }
                Verbose("CreateFolder -- Already Exists {0}", folder);
            }
        }

        internal void RemovePackageSource(string id) {
            var config = Config;
            var source = config.XPathSelectElements(string.Format("/chocolatey/sources/source[@id='{0}']", id)).FirstOrDefault();
            if (source != null) {
                source.Remove();
                Config = config;
            }
        }

        internal void AddPackageSource(string name, string location, bool isTrusted, bool isValidated) {
            if (SkipValidate || ValidateSourceLocation(location)) {
                var config = Config;
                var sources = config.XPathSelectElements("/chocolatey/sources").FirstOrDefault();
                if (sources == null) {
                    config.Root.Add(sources = new XElement("sources"));
                }
                var source = new XElement("source");
                source.SetAttributeValue("id", name);
                source.SetAttributeValue("value", location);
                if (isValidated) {
                    source.SetAttributeValue("validated", true);
                }
                if (isTrusted) {
                    source.SetAttributeValue("trusted", true);
                }
                sources.Add(source);
                Config = config;

                // Yield this from the provider object.
                //YieldPackageSource(name, location, isTrusted, true, isValidated);
            }
        }

        public bool GenerateBins(string pkgPath) {
            var exes = Directory.EnumerateFiles(pkgPath, "*.exe", SearchOption.AllDirectories);
            foreach (var exe in exes) {
                if (File.Exists((exe + ".ignore"))) {
                    continue;
                }
                if (File.Exists(exe + ".gui")) {
                    GenerateGuiBin(exe);
                    continue;
                }
                GenerateConsoleBin(exe);
            }
            return true;
        }

        internal bool Invoke(string script) {
            using (var p = PowerShell.Create(RunspaceMode.NewRunspace)) {
                p.Runspace.SessionStateProxy.SetVariable("request", this);
                p.AddScript(HelperModuleText, false);
                p.AddScript(script);

                foreach (var result in p.Invoke().Where(result => result != null)) {
                    try {
                        Verbose(result.ToString());
                    } catch {
                        // no worries.
                    }
                }
                // todo: I'm seeing cases here were we're getting 'HadErrors == true' but can't find
                // the error.
                // disabling until I can find out why, or replace it with DynamicPowerShell and deal with the errors
                /*
                if (p.HadErrors ) {
                    return false;
                }*
                 */
            }
            return true;
        }

        internal bool InvokeChocolateyScript(string path, string workingDirectory) {
            var pwd = Directory.GetCurrentDirectory();

            try {
                workingDirectory = string.IsNullOrEmpty(workingDirectory) ? pwd : workingDirectory;

                if (Directory.Exists(workingDirectory)) {
                    Directory.SetCurrentDirectory(workingDirectory);
                }
                if (File.Exists(path)) {
                    path = Path.GetFullPath(path);
                    return Invoke(path);
                }
            } catch (Exception e) {
                e.Dump(this);
            } finally {
                Directory.SetCurrentDirectory(pwd);
            }
            return false;
        }

        [SuppressMessage("Microsoft.Performance", "CA1811:AvoidUncalledPrivateCode", Justification = "Required.")]
        public bool GetChocolateyWebFile(string packageName, string fileFullPath, string url, string url64bit) {
            Debug("Calling 'ChocolateyRequest::GetChocolateyWebFile' '{0}','{1}','{2}','{3}' ", packageName, fileFullPath, url, url64bit);

            if (!string.IsNullOrEmpty(url64bit) && Environment.Is64BitOperatingSystem && !ForceX86) {
                url = url64bit;
            }

            Verbose("GetChocolateyWebFile {0} => {1}", packageName, url);

            var uri = new Uri(url);

            ProviderServices.DownloadFile(uri, fileFullPath, this);
            if (string.IsNullOrEmpty(fileFullPath) || !fileFullPath.FileExists()) {
                throw new Exception("Failed to download file {0}".format(url));
            }

            return true;
        }

        [SuppressMessage("Microsoft.Performance", "CA1811:AvoidUncalledPrivateCode", Justification = "Required.")]
        public bool InstallChocolateyInstallPackage(string packageName, string fileType, string silentArgs, string file, int[] validExitCodes, string workingDirectory) {
            Debug("Calling 'ChocolateyRequest::InstallChocolateyInstallPackage' '{0}','{1}','{2}','{3}','{4}','{5}' ", packageName, fileType, silentArgs, file,
                validExitCodes.Select(each => each.ToString()).SafeAggregate((current, each) => current + "," + each), workingDirectory);

            switch (fileType.ToLowerInvariant()) {
                case "msi":
                case "msu":
                    return ProviderServices.Install(file, silentArgs, this);

                case "exe":
                    return StartChocolateyProcessAsAdmin("{0}".format(silentArgs), file, true, true, validExitCodes, workingDirectory);
            }
            return false;
        }

        [SuppressMessage("Microsoft.Performance", "CA1811:AvoidUncalledPrivateCode", Justification = "Required.")]
        public bool InstallChocolateyPackage(string packageName, string fileType, string silentArgs, string url, string url64bit, int[] validExitCodes, string workingDirectory) {
            Debug("Calling 'ChocolateyRequest::InstallChocolateyPackage' '{0}','{1}','{2}','{3}','{4}','{5}','{6}' ", packageName, fileType, silentArgs, url, url64bit,
                validExitCodes.Select(each => each.ToString()).SafeAggregate((current, each) => current + "," + each), workingDirectory);

            try {
                var tempFolder = Path.GetTempPath();
                ;
                var chocTempDir = Path.Combine(tempFolder, "chocolatey");
                var pkgTempDir = Path.Combine(chocTempDir, packageName);
                Delete(pkgTempDir);
                CreateFolder(pkgTempDir);

                if (!string.IsNullOrEmpty(url64bit) && Environment.Is64BitOperatingSystem && !ForceX86) {
                    url = url64bit;
                }
                string localFile = null;

                try {
                    localFile = url.CanonicalizePath(!string.IsNullOrWhiteSpace(workingDirectory));

                    // check to see if the url is a local file
                    if (!localFile.FileExists()) {
                        localFile = null;
                    }
                } catch {
                    // not a local file.
                }
                if (string.IsNullOrEmpty(localFile)) {
                    localFile = Path.Combine(pkgTempDir, "{0}install.{1}".format(packageName, fileType));
                    if (!GetChocolateyWebFile(packageName, localFile, url, url64bit)) {
                        throw new Exception(string.Format("Download failed {0} {1} {2}", url, url64bit, localFile));
                    }
                }

                if (InstallChocolateyInstallPackage(packageName, fileType, silentArgs, localFile, validExitCodes, workingDirectory)) {
                    Verbose("Package Successfully Installed {0}", packageName);
                    return true;
                }
                throw new Exception("Failed Install.");
            } catch (Exception e) {
                e.Dump(this);
                Error(ErrorCategory.InvalidResult, packageName, Constants.Messages.DependentPackageFailedInstall, packageName);

                throw new Exception("Failed Installation");
            }
        }

        [SuppressMessage("Microsoft.Performance", "CA1811:AvoidUncalledPrivateCode", Justification = "Required.")]
        public Snapshot SnapshotFolder(string locationToMonitor) {
            return new Snapshot(this, locationToMonitor);
        }

        [SuppressMessage("Microsoft.Performance", "CA1811:AvoidUncalledPrivateCode", Justification = "Required.")]
        public bool InstallChocolateyPath(string pathToInstall, string context) {
            Debug("Calling 'ChocolateyRequest::InstallChocolateyPath' '{0}','{1}'", pathToInstall, context);
            if (context.Equals("machine", StringComparison.InvariantCultureIgnoreCase)) {
                if (IsElevated) {
                    EnvironmentUtility.SystemPath = EnvironmentUtility.SystemPath.Append(pathToInstall).RemoveMissingFolders();
                    EnvironmentUtility.Path = EnvironmentUtility.Path.Append(pathToInstall).RemoveMissingFolders();
                    return true;
                }
                Verbose("Elevation Required--May not modify system path without elevation");
                return false;
            }
            EnvironmentUtility.UserPath = EnvironmentUtility.UserPath.Append(pathToInstall).RemoveMissingFolders();
            EnvironmentUtility.Path = EnvironmentUtility.Path.Append(pathToInstall).RemoveMissingFolders();
            return true;
        }

        [SuppressMessage("Microsoft.Performance", "CA1811:AvoidUncalledPrivateCode", Justification = "Required.")]
        public void UpdateSessionEnvironment() {
            Debug("Calling 'ChocolateyRequest::UpdateSessionEnvironment'");
            EnvironmentUtility.Rehash();
        }

        public string GetBatFileLocation(string exe, string name) {
            Debug("Calling 'ChocolateyRequest::GetBatFileLocation' '{0}','{1}'", exe, name);
            if (string.IsNullOrEmpty(name)) {
                return Path.Combine(PackageExePath, Path.GetFileNameWithoutExtension(exe) + ".bat");
            } else {
                return Path.Combine(PackageExePath, Path.GetFileNameWithoutExtension(name) + ".bat");
            }
        }

        [SuppressMessage("Microsoft.Performance", "CA1811:AvoidUncalledPrivateCode", Justification = "Can be called from powershell")]
        public void GeneratePS1ScriptBin(string ps1, string name = null) {
            Debug("Calling 'ChocolateyRequest::GeneratePS1ScriptBin' '{0}','{1}'", ps1, name);

            File.WriteAllText(GetBatFileLocation(ps1, name), @"@echo off
powershell -NoProfile -ExecutionPolicy unrestricted -Command ""& '{0}'  %*""".format(ps1));
        }

        public void GenerateConsoleBin(string exe, string name = null) {
            Debug("Calling 'ChocolateyRequest::GenerateConsoleBin' '{0}','{1}'", exe, name);
            File.WriteAllText(GetBatFileLocation(exe, name), @"@echo off
SET DIR=%~dp0%
cmd /c ""%DIR%{0} %*""
exit /b %ERRORLEVEL%".format(PackageExePath.RelativePathTo(exe)));
        }

        public void GenerateGuiBin(string exe, string name = null) {
            Debug("Calling 'ChocolateyRequest::GenerateGuiBin' '{0}','{1}'", exe, name);
            File.WriteAllText(GetBatFileLocation(exe, name), @"@echo off
SET DIR=%~dp0%
start """" ""%DIR%{0}"" %*".format(PackageExePath.RelativePathTo(exe)));
        }

        [SuppressMessage("Microsoft.Performance", "CA1811:AvoidUncalledPrivateCode", Justification = "Required.")]
        public bool RemoveBins(string pkgPath) {
            Debug("Calling 'ChocolateyRequest::RemoveBins' '{0}'", pkgPath);
            var exes = Directory.EnumerateFiles(pkgPath, "*.exe", SearchOption.AllDirectories);
            foreach (var exe in exes) {
                if (File.Exists(exe + ".ignore")) {
                    continue;
                }
                if (File.Exists(exe + ".gui")) {
                    RemoveGuiBin(exe);
                    continue;
                }
                RemoveConsoleBin(exe);
            }
            return true;
        }

        [SuppressMessage("Microsoft.Performance", "CA1811:AvoidUncalledPrivateCode", Justification = "Required.")]
        public void RemoveConsoleBin(string exe, string name = null) {
            Debug("Calling 'ChocolateyRequest::RemoveConsoleBin' '{0}','{1}'", exe, name);
            Delete(GetBatFileLocation(exe, name));
        }

        [SuppressMessage("Microsoft.Performance", "CA1811:AvoidUncalledPrivateCode", Justification = "Required.")]
        public void RemoveGuiBin(string exe, string name = null) {
            Debug("Calling 'ChocolateyRequest::RemoveGuiBin' '{0}','{1}'", exe, name);
            Delete(GetBatFileLocation(exe, name));
        }

        [SuppressMessage("Microsoft.Performance", "CA1811:AvoidUncalledPrivateCode", Justification = "Required.")]
        public bool InstallChocolateyPowershellCommand(string packageName, string psFileFullPath, string url, string url64bit, string workingDirectory) {
            Debug("Calling 'ChocolateyRequest::InstallChocolateyPowershellCommand' '{0}','{1}','{2}','{3}','{4}'", packageName, psFileFullPath, url, url64bit, workingDirectory);
            if (GetChocolateyWebFile(packageName, psFileFullPath, url, url64bit)) {
                if (File.Exists(psFileFullPath)) {
                    GeneratePS1ScriptBin(psFileFullPath);
                    return true;
                }
            }

            Verbose("Unable to download script {0}", url);
            return false;
        }

        [SuppressMessage("Microsoft.Performance", "CA1811:AvoidUncalledPrivateCode", Justification = "Required.")]
        public bool InstallChocolateyVsixPackage(string packageName, string vsixUrl, string vsVersion) {
            Debug("Calling 'ChocolateyRequest::InstallChocolateyVsixPackage' '{0}','{1}','{2}'", packageName, vsixUrl, vsVersion);

            var vs = Registry.LocalMachine.OpenSubKey(@"Software\Wow6432Node\Microsoft\VisualStudio");
            var versions = vs.GetSubKeyNames().Select(each => {
                float f;
                if (!float.TryParse(each, out f)) {
                    return null;
                }
                if (f < 10.0) {
                    return null;
                }

                var vsv = vs.OpenSubKey(each);
                if (vsv.GetValueNames().Contains("InstallDir", StringComparer.OrdinalIgnoreCase)) {
                    return new {
                        Version = f,
                        InstallDir = vsv.GetValue("InstallDir").ToString()
                    };
                }
                return null;
            }).Where(each => each != null).OrderByDescending(each => each.Version);

            var reqVsVersion = versions.FirstOrDefault();

            if (!string.IsNullOrEmpty(vsVersion)) {
                float f;
                if (!float.TryParse(vsVersion, out f)) {
                    throw new Exception("Unable to parse version number");
                }

                reqVsVersion = versions.FirstOrDefault(each => each.Version == f);
            }

            if (reqVsVersion == null) {
                throw new Exception("Required Visual Studio Version is not installed");
            }

            var vsixInstller = Path.Combine(reqVsVersion.InstallDir, "VsixInstaller.exe");
            if (!File.Exists(vsixInstller)) {
                throw new Exception("Can't find Visual Studio VSixInstaller.exe {0}".format(vsixInstller));
            }
            var file = Path.Combine(Path.GetTempPath(), packageName.MakeSafeFileName());

            ProviderServices.DownloadFile(new Uri(vsixUrl), file, this);

            if (string.IsNullOrEmpty(file) || !File.Exists(file)) {
                throw new Exception("Unable to download file {0}".format(vsixUrl));
            }
            var process = AsyncProcess.Start(new ProcessStartInfo {
                FileName = vsixInstller,
                Arguments = @"/q ""{0}""".format(file),
            });
            process.WaitForExit();
            if (process.ExitCode > 0 && process.ExitCode != 1001) {
                Verbose("VsixInstall Failure {0}", file);
                throw new Exception("Install failure");
            }
            return false;
        }

        [SuppressMessage("Microsoft.Performance", "CA1811:AvoidUncalledPrivateCode", Justification = "Required.")]
        public bool InstallChocolateyExplorerMenuItem(string menuKey, string menuLabel, string command, string type) {
            Debug("Calling 'ChocolateyRequest::InstallChocolateyExplorerMenuItem' '{0}','{1}','{2}','{3}'", menuKey, menuLabel, command, type);

            var key = type == "file" ? "*" : (type == "directory" ? "directory" : null);
            if (key == null) {
                return false;
            }
            if (!IsElevated) {
                return StartChocolateyProcessAsAdmin("Install-ChocolateyExplorerMenuItem '{0}' '{1}' '{2}' '{3}'".format(menuKey, menuLabel, command, type), "powershell", false, false, new[] {
                    0
                }, Environment.CurrentDirectory);
            }

            var k = Registry.ClassesRoot.CreateSubKey(@"{0}\shell\{1}".format(key, menuKey));
            k.SetValue(null, menuLabel);
            var c = k.CreateSubKey("command");
            c.SetValue(null, @"{0} ""%1""");
            return true;
        }

        [SuppressMessage("Microsoft.Performance", "CA1811:AvoidUncalledPrivateCode", Justification = "Required.")]
        public bool UninstallChocolateyPackage(string packageName, string fileType, string silentArgs, string file, int[] validExitCodes, string workingDirectory) {
            Debug("Calling 'ChocolateyRequest::UninstallChocolateyPackage' '{0}','{1}','{2}','{3}','{4}','{5}' ", packageName, fileType, silentArgs, file, validExitCodes.Select(each => each.ToString()).SafeAggregate((current, each) => current + "," + each),
                workingDirectory);

            switch (fileType.ToLowerInvariant()) {
                case "msi":
                    return StartChocolateyProcessAsAdmin("/x {0} {1}".format(file, silentArgs), "msiexec.exe", true, true, validExitCodes, workingDirectory);

                case "exe":
                    return StartChocolateyProcessAsAdmin("{0}".format(silentArgs), file, true, true, validExitCodes, workingDirectory);

                default:
                    Verbose("Unsupported Uninstall Type {0}", fileType);
                    break;
            }
            return false;
        }

        [SuppressMessage("Microsoft.Performance", "CA1811:AvoidUncalledPrivateCode", Justification = "Required.")]
        public string GetChocolateyUnzip(string fileFullPath, string destination, string specificFolder, string packageName) {
            Debug("Calling 'ChocolateyRequest::GetChocolateyUnzip' '{0}','{1}','{2}','{3}'", fileFullPath, destination, specificFolder, packageName);

            try {
                var zipfileFullPath = fileFullPath;

                if (!string.IsNullOrEmpty(specificFolder)) {
                    fileFullPath = Path.Combine(fileFullPath, specificFolder);
                }

                if (!string.IsNullOrEmpty(packageName)) {
                    var packageLibPath = Environment.GetEnvironmentVariable("ChocolateyPackageFolder");
                    CreateFolder(packageLibPath);
                    var zipFileName = Path.GetFileName(zipfileFullPath);
                    var zipExtractLogFullPath = Path.Combine(packageLibPath, "{0}.txt".format(zipFileName));
                    var snapshot = new Snapshot(this, destination);

                    // UnZip(fileFullPath, destination);
                    var files = ProviderServices.UnpackArchive(fileFullPath, destination, this).ToArray();

                    snapshot.WriteFileDiffLog(zipExtractLogFullPath);
                } else {
                    var files = ProviderServices.UnpackArchive(fileFullPath, destination, this).ToArray();
                }
                return destination;
            } catch (Exception e) {
                e.Dump(this);
                Verbose("PackageInstallation Failed {0}", packageName);
                throw new Exception("Failed Installation");
            }
        }

        [SuppressMessage("Microsoft.Performance", "CA1811:AvoidUncalledPrivateCode", Justification = "Required.")]
        public bool InstallChocolateyZipPackage(string packageName, string url, string unzipLocation, string url64bit, string specificFolder, string workingDirectory) {
            Debug("Calling 'ChocolateyRequest::InstallChocolateyZipPackage' '{0}','{1}','{2}','{3}','{4}','{5}' ", packageName, url, unzipLocation, url64bit, specificFolder, workingDirectory);
            try {
                var tempFolder = Path.GetTempPath();
                ;
                var chocTempDir = Path.Combine(tempFolder, "chocolatey");
                var pkgTempDir = Path.Combine(chocTempDir, packageName);
                Delete(pkgTempDir);
                CreateFolder(pkgTempDir);

                var file = Path.Combine(pkgTempDir, "{0}install.{1}".format(packageName, "zip"));
                if (GetChocolateyWebFile(packageName, file, url, url64bit)) {
                    if (!string.IsNullOrEmpty(GetChocolateyUnzip(file, unzipLocation, specificFolder, packageName))) {
                        Verbose("Package Successfully Installed", packageName);
                        return true;
                    }
                    throw new Exception("Failed Install.");
                }
                throw new Exception("Failed Download.");
            } catch (Exception e) {
                e.Dump(this);
                Verbose("PackageInstallation Failed {0}", packageName);
                throw new Exception("Failed Installation");
            }
        }

        [SuppressMessage("Microsoft.Performance", "CA1811:AvoidUncalledPrivateCode", Justification = "Required.")]
        public bool UnInstallChocolateyZipPackage(string packageName, string zipFileName) {
            Debug("Calling 'ChocolateyRequest::UnInstallChocolateyZipPackage' '{0}','{1}' ", packageName, zipFileName);
            try {
                var packageLibPath = Environment.GetEnvironmentVariable("ChocolateyPackageFolder");
                var zipContentFile = Path.Combine(packageLibPath, "{0}.txt".format(Path.GetFileName(zipFileName)));
                if (File.Exists(zipContentFile)) {
                    foreach (var file in File.ReadAllLines(zipContentFile).Where(each => !string.IsNullOrEmpty(each) && File.Exists(each))) {
                        Delete(file);
                    }
                }
            } catch (Exception e) {
                e.Dump(this);
                Verbose("uninstall failure {0}", packageName);
            }
            return true;
        }

        [SuppressMessage("Microsoft.Performance", "CA1811:AvoidUncalledPrivateCode", Justification = "Required.")]
        public bool InstallChocolateyFileAssociation(string extension, string executable) {
            Debug("Calling 'ChocolateyRequest::InstallChocolateyFileAssociation' '{0}','{1}' ", extension, executable);
            if (string.IsNullOrEmpty(executable)) {
                throw new ArgumentNullException("executable");
            }

            if (string.IsNullOrEmpty(extension)) {
                throw new ArgumentNullException("extension");
            }
            executable = Path.GetFullPath(executable);
            if (!File.Exists(executable)) {
                throw new FileNotFoundException("Executable not found", executable);
            }

            extension = "." + extension.Trim().Trim('.');
            var fileType = Path.GetFileName(executable).Replace(' ', '_');

            return StartChocolateyProcessAsAdmin(@"/c assoc {0}={1} & ftype {1}={2} ""%1"" %*".format(extension, fileType, executable), "cmd.exe", false, false, new[] {
                0
            }, Environment.CurrentDirectory);
        }

        [SuppressMessage("Microsoft.Performance", "CA1811:AvoidUncalledPrivateCode", Justification = "Required.")]
        public bool InstallChocolateyPinnedTaskBarItem(string targetFilePath) {
            Debug("Calling 'ChocolateyRequest::InstallChocolateyPinnedTaskBarItem' '{0}'", targetFilePath);

            if (string.IsNullOrEmpty(targetFilePath)) {
                Verbose("Failed InstallChocolateyPinnedTaskBarItem -- Empty path");
                throw new Exception("Failed.");
            }

            AddPinnedItemToTaskbar(Path.GetFullPath(targetFilePath));
            return true;
        }

        [SuppressMessage("Microsoft.Performance", "CA1811:AvoidUncalledPrivateCode", Justification = "Required.")]
        public bool StartChocolateyProcessAsAdmin(string statements, string exeToRun, bool minimized, bool noSleep, int[] validExitCodes, string workingDirectory) {
            Debug("Calling 'ChocolateyRequest::XXXX' '{0}','{1}','{2}','{3}','{4}','{5}' ", statements, exeToRun, minimized, noSleep, validExitCodes.Select(each => each.ToString()).SafeAggregate((current, each) => current + "," + each), workingDirectory);

            if (exeToRun.EqualsIgnoreCase("powershell")) {
                // run as a powershell script
                if (IsElevated) {
                    Verbose("Already Elevated - Running PowerShell script in process");
                    // in proc, we're already good.
                    return Invoke(statements);
                }

                Verbose("Not Elevated - Running PowerShell script in new process");
                // otherwise setup a new proc
                Error(ErrorCategory.InvalidOperation, statements, "Unable to elevate process (this prototype can't do that right now)");
                return false;
            }

            // just a straight exec from here.
            try {
                Verbose("Launching Process-EXE :'{0}'", exeToRun);
                var process = AsyncProcess.Start(new ProcessStartInfo {
                    FileName = exeToRun,
                    Arguments = statements,
                    WorkingDirectory = workingDirectory,
                    WindowStyle = minimized ? ProcessWindowStyle.Hidden : ProcessWindowStyle.Normal,
                    Verb = IsElevated ? "" : "runas",
                });

                while (!process.WaitForExit(1)) {
                    if (IsCanceled) {
                        process.Kill();
                        Verbose("Process Killed - Host requested cancellation");
                        throw new Exception("Killed Process {0}".format(exeToRun));
                    }
                }

                if (validExitCodes.Contains(process.ExitCode)) {
                    Verbose("Process Exited Successfully.", "{0}", exeToRun);
                    return true;
                }
                Verbose("Process Failed {0}", exeToRun);
                throw new Exception("Process Exited with non-successful exit code {0} : {1} ".format(exeToRun, process.ExitCode));
            } catch (Exception e) {
                e.Dump(this);

                Error("Process Execution Failed", "'{0}' -- {1}", exeToRun, e.Message);
                throw e;
            }
        }

        internal class PackagesEnumerable : IEnumerable<IPackage> {
            private IQueryable<IPackage> _packages;

            internal PackagesEnumerable(IQueryable<IPackage> packages) {
                _packages = packages;
            }

            public IEnumerator<IPackage> GetEnumerator() {
                return new PackageEnumerator(_packages);
            }

            IEnumerator IEnumerable.GetEnumerator() {
                return GetEnumerator();
            }
        }

        internal class PackageEnumerator : IEnumerator<IPackage> {
            private bool _done;
            private int _index;
            private Task<IPackage[]> _nextSet;
            private IQueryable<IPackage> _packages;
            private IPackage[] _page;
            private int _resultIndex;

            internal PackageEnumerator(IQueryable<IPackage> packages) {
                _packages = packages;
                Reset();
                PullNextSet();
            }

            public void Dispose() {
                _done = true;
            }

            public bool MoveNext() {
                _index++;

                if (_index >= _page.Length && !_done) {
                    _index = 0;
                    // _page = _packages.Skip(_resultIndex).Take(40).ToArray();
                    _page = _nextSet.Result;
                    _resultIndex += _page.Length;
                    if (_page.Length == 0) {
                        _done = true;
                    } else {
                        PullNextSet();
                    }
                }

                if (_index >= _page.Length) {
                    return false;
                }

                return true;
            }

            public void Reset() {
                _done = false;
                _page = new IPackage[0];
                ;
                _index = -1;
                _resultIndex = 0;
            }

            public IPackage Current {
                get {
                    return _page[_index];
                }
            }

            object IEnumerator.Current {
                get {
                    return Current;
                }
            }

            private void PullNextSet() {
                _nextSet = Task.Factory.StartNew(() => {return _packages.Skip(_resultIndex).Take(40).ToArray();});
            }
        }

        internal static ImplictLazy<string> ChocolateyModuleFolder = new ImplictLazy<string>(() => Path.GetFullPath(Assembly.GetExecutingAssembly().Location));
        internal static ImplictLazy<string> ChocolateyModuleFile = new ImplictLazy<string>(() => Path.Combine(ChocolateyModuleFolder, "Chocolatey.psd1"));
        internal static ImplictLazy<string> EtcPath = new ImplictLazy<string>(() => Path.Combine(ChocolateyModuleFolder, "etc"));
        internal static ImplictLazy<string> ChocolateyConfigPath = new ImplictLazy<string>(() => Path.Combine(RootInstallationPath, "chocolateyinstall", "Chocolatey.config"));

        internal static ImplictLazy<string> SystemDrive = new ImplictLazy<string>(() => {
            var drive = Environment.GetEnvironmentVariable("SystemDrive");

            if (string.IsNullOrEmpty(drive)) {
                return "c:\\";
            }
            return drive + "\\";
        });

        internal static ImplictLazy<string> RootInstallationPath = new ImplictLazy<string>(() => {
            var rip = Environment.GetEnvironmentVariable("ChocolateyPath");
            if (string.IsNullOrEmpty(rip)) {
                // current default
                rip = Path.Combine(SystemDrive, @"\", "Chocolatey");

                // store it.
                Environment.SetEnvironmentVariable("ChocolateyPath", rip, EnvironmentVariableTarget.User);
                Environment.SetEnvironmentVariable("ChocolateyPath", rip, EnvironmentVariableTarget.Process);
            }

            if (!rip.DirectoryHasDriveLetter()) {
                rip = rip.TrimStart('\\');
                rip = Path.Combine(SystemDrive, rip);
                Environment.SetEnvironmentVariable("ChocolateyPath", rip, EnvironmentVariableTarget.User);
                Environment.SetEnvironmentVariable("ChocolateyPath", rip, EnvironmentVariableTarget.Process);
            }
            if (!Directory.Exists(rip)) {
                Directory.CreateDirectory(rip);
            }
            return rip;
        });
    }

    internal enum InstallStatus {
        Unknown,
        Successful,
        Failed,
        AlreadyPresent
    }

    internal class InstallResult : Dictionary<InstallStatus, List<PackageItem>> {
        internal InstallStatus Status = InstallStatus.Unknown;
    }
}