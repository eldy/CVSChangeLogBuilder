#!/usr/bin/perl
#-------------------------------------------------------
# Build a changelog file for a CVS project
# Serveral output format are available
#-------------------------------------------------------
# $Revision$ - $Author$ - $Date$
use strict; no strict "refs";
use Time::Local;
#use diagnostics;


#-------------------------------------------------------
# Defines
#-------------------------------------------------------
my $REVISION='$Revision$'; $REVISION =~ /\s(.*)\s/; $REVISION=$1;
my $VERSION="1.1 (build $REVISION)";

# ---------- Init variables --------
use vars qw/ $TagStart $Branch $TagEnd /;
my $Debug=0;
my $DIR;
my $PROG;
my $Extension;
my $Help='';
my $TagStart='';
my $TagEnd='';
my $Module='';
my $Output='';		# Default will be "listdeltabydate"
my $CvsRoot='';		# Example ":ntserver:127.0.0.1:d:/temp/cvs"
my $UseSsh=0;
my $RLogFile;
my $RepositoryPath;
my $nowtime = my $nowweekofmonth = my $nowdaymod = my $nowsmallyear = 0; 
my $nowsec = my $nowmin = my $nowhour = my $nowday = my $nowmonth = my $nowyear = my $nowwday = 0;
my $filename='';
my %filesym=();
my $fileversion='';
my $filedate='';
my $fileauthor='';
my $filestate='';
my $filechange='';
my $filelog='';
my $oldfiledayauthor='';
my $oldfilelog='';
my $EXTRACTFILENAME="^RCS file: (.+)";
my $EXTRACTSYMBOLICNAMEAREA="symbolic names:";
my $EXTRACTSYMBOLICNAMEENTRY="^\\s(.+): ([\\d\\.]+)";
my $EXTRACTFILEVERSION="^revision (.+)";
my $EXTRACTFILEDATEAUTHORSTATE="date: (.+)\\sauthor: (.*)\\sstate: ([^\\s]+)(.*)";
my $CVSCLIENT="cvs";
# ---------- Init hash arrays --------
# For all
my %maxincludedver=();
my %minexcludedver=();
# For output by date
my %DateAuthorChange=();
my %DateAuthorLogChange=();
my %DateAuthorLogFileRevChange=();
# For output by file
my %FilesLastVersion=();
my %FilesChangeDate=();
my %FilesChangeAuthor=();
my %FilesChangeState=();
my %FilesChangeLog=();
# For output by log
my $LGMAXLOG=400;
my %LogChange=();
my %LogChangeDate=();
my %LogChangeAuthor=();
my %LogChangeState=();




#-------------------------------------------------------
# Functions
#-------------------------------------------------------

#-------------------------------------------------------
# Error
#-------------------------------------------------------
sub error {
	print "Error: $_[0]\n";
    exit 1;
}

#-------------------------------------------------------
# Debug
#-------------------------------------------------------
sub debug {
	my $level = $_[1] || 1;
	if ($Debug >= $level) { 
		my $debugstring = $_[0];
		if ($ENV{"GATEWAY_INTERFACE"}) { $debugstring =~ s/^ /&nbsp&nbsp /; $debugstring .= "<br>"; }
		print "DEBUG $level - ".time." : $debugstring\n";
		}
	0;
}

#-------------------------------------------------------
# LoadDataInMemory
# Add entries in Hash arrays
#-------------------------------------------------------
sub LoadDataInMemory {

	# Define filename
	#my $newfilename=ExcludeRepositoryFromPath("$filename");
	my $newfilename=$filename;

	# Define filelog
	my $newfilelog="$filelog";
	$newfilelog =~ s/\n\s*\n/\n/g;					# Remove blank lines

	# DEFINE CHANGE STATUS (removed, changed or added) OF FILE
	my $newfilestate='';
	if ($Output =~ /^listdelta/) {
		if ($Branch) {
			# We want a delta in a secondary BRANCH: Change status can't be defined
			if (!$filesym{$filename}{$Branch}) { return; }		# This entry is not in branch 
			$newfilestate="unknown";
		}
		else {
			# We want a delta in main BRANCH
			if ($TagStart && $filesym{$filename}{$TagStart}) {
				# File did exist at the beginning
				if ($TagEnd && ! $filesym{$filename}{$TagEnd}) {	# File was removed between TagStart and TagEnd
					$newfilestate="removed";
				}
				else {
					if ($filestate !~ /dead/) {
						$newfilestate="changed";
					}
					else {
						$newfilestate="removed";
					}
				}
			}
			else {
				# File did not exist at the beginning
				if (! $TagEnd || $filesym{$filename}{$TagEnd}) {		# File was added after TagStart (and before TagEnd)
					# If file contains Attic, this means it was deleted so, as it didn't exists in start tag version,
					# this means we can ignore this file.
					if ($filename =~ /[\\\/]Attic([\\\/][^\\\/]+)/) { return; }
					if ($filestate !~ /dead/) {
						if ($filechange) {
							$newfilestate="changed";	# Sometimes it should be "added" (if added after a remove). This will be corrected later.
						}
						else {	# A file added after TagStart
							$newfilestate="added";
						}
					}
					else {
						$newfilestate="removed";
					}
				}
				else {
					$newfilestate="removed";
					return;
				}
			}
		}
	}
	debug(">> File revision $newfilename $fileversion $filedate $fileauthor $filestate $filechange is action '$newfilestate'",3);
	
	# For output by date
	if ($Output =~ /bydate/ || $Output =~ /forrpm/) {
		my $fileday=$filedate; $fileday =~ s/\s.*//g;
		$DateAuthorChange{"$fileday $fileauthor"}=1;
		$DateAuthorLogChange{"$fileday $fileauthor"}{$newfilelog}=1;
		$DateAuthorLogFileRevChange{"$fileday $fileauthor"}{$newfilelog}{"$newfilename $fileversion"}=$newfilestate;
		if ($newfilestate eq "removed") {
			# Change a state of a revision from "changed" into "added" when previous revision was "removed"
			my $fileversionnext=$fileversion;
			if ($fileversionnext =~ /\.(\d+)$/) {
				my $newver=int($1)+1;
				$fileversionnext =~ s/\.(\d+)$/\.$newver/;
			}
			if ($DateAuthorLogFileRevChange{$oldfiledayauthor}{$oldfilelog}{"$newfilename $fileversionnext"} =~ /^changed$/) {
				debug("Correct next version of $newfilename $fileversionnext ($fileversionnext should be 'added_forced' instead of 'changed')",2);
				$DateAuthorLogFileRevChange{$oldfiledayauthor}{$oldfilelog}{"$newfilename $fileversionnext"}="added_forced";
			}
		}
		# When a version file does not exists in end, all versions are at state 'removed'.
		# We must change this into "changed" for those whose next revision exists and is 'removed'. Only last one keeps 'removed'.
		if ($newfilestate eq "removed") {
			my $fileversionnext=$fileversion;
			if ($fileversionnext =~ /\.(\d+)$/) {
				my $newver=int($1)+1;
				$fileversionnext =~ s/\.(\d+)$/\.$newver/;
			}
			if ($DateAuthorLogFileRevChange{$oldfiledayauthor}{$oldfilelog}{"$newfilename $fileversionnext"} =~ /^(removed|changed_forced)$/) {
				debug("Correct version of $newfilename $fileversion ($fileversion should be 'changed_forced' instead of 'removed')",2);
				$DateAuthorLogFileRevChange{"$fileday $fileauthor"}{$newfilelog}{"$newfilename $fileversion"}='changed_forced';	# with _forced to not be change again by previous test
			}
		}
		# Var used to retrieve easily the revision already read just before the one processed in this function
		$oldfiledayauthor="$fileday $fileauthor";
		$oldfilelog="$newfilelog";
	}
	
	# For output by file
	if ($Output =~ /byfile/) {
		if (! $FilesLastVersion{$newfilename}) { $FilesLastVersion{$newfilename}=$fileversion; }	# Save 'last' file version
		$FilesChangeDate{$newfilename}{$fileversion}=$filedate;
		$FilesChangeAuthor{$newfilename}{$fileversion}=$fileauthor;
		$FilesChangeState{$newfilename}{$fileversion}=$newfilestate;
		$FilesChangeLog{$newfilename}{$fileversion}=$newfilelog;
	}
	
	# For output by log
	if ($Output =~ /bylog/) {
		$LogChange{$newfilelog}=1;
		$LogChangeDate{$newfilelog}{"$newfilename $fileversion"}=$filedate;
		$LogChangeAuthor{$newfilelog}{"$newfilename $fileversion"}=$fileauthor;
		$LogChangeState{$newfilelog}{"$newfilename $fileversion"}=$newfilestate;
	}
}

#------------------------------------------------------------------------------
# Function:      Format a date
# Input:         String "YYYY/MM/DD HH:MM:SS xxx"
#                Option "" or "rpm"
# Return:        string "YYYY-MM-DD HH:MM:SS xxx" if option is ""
#                String "Thu Mar 7 2002 xxx" if option is "rpm"
#------------------------------------------------------------------------------
sub FormatDate {
	my $string=shift;
	my $option=shift;
	$string =~ s/\//\-/g;
	if ($option eq 'rpm' && $string =~ /(\d\d\d\d)-(\d\d)-(\d\d)/) {
		my $ns=Time::Local::timelocal(0,0,0,$3,$2-1,$1);
		my $ctime=localtime($ns); $ctime =~ s/ 00:00:00//;
		$string =~ s/(\d\d\d\d)-(\d\d)-(\d\d)/$ctime/;
	}
	return "$string";
}

#------------------------------------------------------------------------------
# Function:      Compare 2 CVS version number
# Input:         $a $b
# Output:        -1 if $a < $b, 1 if $a >= $b
#------------------------------------------------------------------------------
sub CompareVersion {
	my $a=shift;
	my $b=shift;
	my $aint; my $adec; my $bint; my $bdec;
	if ($a =~ /^(\d+)\.(\d+)$/) { $aint=int($1); $adec=int($2); } else { $aint=int($a); $adec=0; }
	if ($b =~ /^(\d+)\.(\d+)$/) { $bint=int($1); $bdec=int($2); } else { $bint=int($b); $bdec=0; }
	if ($aint < $bint) { return -1; }
	if ($aint > $bint) { return 1; }
	if ($adec < $bdec) { return -1; }
	return 1;
}

#------------------------------------------------------------------------------
# Function:      Compare 2 CVS version number
# Input:         $a $b
# Output:        -1 if $a < $b, 0 if $a = $b, 1 if $a > $b
#------------------------------------------------------------------------------
sub CompareVersionBis {
	my $a=shift;
	my $b=shift;
	my $aint; my $adec; my $bint; my $bdec;
	if ($a =~ /^(\d+)\.(\d+)$/) { $aint=int($1); $adec=int($2); } else { $aint=int($a); $adec=0; }
	if ($b =~ /^(\d+)\.(\d+)$/) { $bint=int($1); $bdec=int($2); } else { $bint=int($b); $bdec=0; }
	if ($aint < $bint) { return -1; }
	if ($aint > $bint) { return 1; }
	if ($adec < $bdec) { return -1; }
	if ($adec > $bdec) { return 1; }
	return 0;
}

sub ExcludeRepositoryFromPath {
	my $file=shift;
	$file =~ s/[\\\/]Attic([\\\/][^\\\/]+)/$1/;
	$file =~ s/^.*[\\\/]$Module[\\\/]//;		# Extract path of repository
	return $file;
}



#-------------------------------------------------------
# MAIN
#-------------------------------------------------------
my $QueryString=''; for (0..@ARGV-1) { $QueryString .= "$ARGV[$_] "; }
if ($QueryString =~ /debug=(\d+)/i)    			{ $Debug=$1; }
if ($QueryString =~ /m(?:odule|)=([^\s]+)/i)	{ $Module=$1; }
if ($QueryString =~ /output=([^\s]+)/i)   		{ $Output=$1; }
if ($QueryString =~ /branch=([^\s]+)/i)			{ $Branch=$1; }
if ($QueryString =~ /tagstart=([^\s]+)/i) 		{ $TagStart=$1; }
if ($QueryString =~ /tagend=([^\s]+)/i)   		{ $TagEnd=$1; }
if ($QueryString =~ /rlogfile=([:\-\.\\\/\wè~]+)/i) { $RLogFile=$1; }
if ($QueryString =~ /-d=([^\s]+)/)      		{ $CvsRoot=$1; }
if ($QueryString =~ /-h/)      					{ $Help=1; }
if ($QueryString =~ /-ssh/)    					{ $UseSsh=1 }
($DIR=$0) =~ s/([^\/\\]*)$//; ($PROG=$1) =~ s/\.([^\.]*)$//; $Extension=$1;
debug("Module: $Module");
debug("Output: $Output");

# On determine chemin complet du repertoire racine et on en deduit les repertoires de travail
my $REPRACINE;
if (! $ENV{"SERVER_NAME"}) {
	$REPRACINE=($DIR?$DIR:".")."/..";
} else {
	$REPRACINE=$ENV{"DOCUMENT_ROOT"};
}

if ($Output) {
	if ($Output ne "listdeltabydate" && $Output ne "listdeltabylog" && $Output ne "listdeltabyfile" && $Output ne "listdeltaforrpm") {
		print "----- $PROG $VERSION (c) Laurent Destailleur -----\n";
		print "Unknown value for output parameter.\n";
		exit 1;
	}
}

if ($Help || ! $Output) {
	print "----- $PROG $VERSION (c) Laurent Destailleur -----\n";
	print "$PROG generates advanced ChangeLog files for CVS projects/modules.\n";
	print "Note 1: Your cvs client (cvs or cvs.exe) must be in your PATH.\n";
	print "Note 2: To use cvs client through ssh, add option -ssh.\n";
	print "\nUsage:\n";
	print "  $PROG.$Extension -output=outputmode [-m=module -d=repository] [options]\n";
	print "\n";
	print "Where 'outputmode' is:\n";
	print "  listdeltabydate  To get a changelog between 2 versions, sorted by date\n";
	print "  listdeltabylog   To get a changelog between 2 versions, sorted by log\n";
	print "  listdeltabyfile  To get a changelog between 2 versions, sorted by file\n";
	print "  listdeltaforrpm  To get a changelog between 2 versions for rpm spec files\n";
	print "\n";
	print "  Note that \"between 2 versions\" means (depending on tagstart/tagend usage):\n";
	print "  * from start to a tagged version (version changes included)\n";
	print "  * from a start version (excluded) to another tagged version (included)\n";
	print "  * or from a tagged version until now (version changes excluded)\n";
	print "\n";
	print "The 'module' and 'repository' are the CVS module name and the CVS repository.\n";
	print "  If current directory is the root of a CVS project built from a cvs checkout,\n";
	print "  cvschangelogbuilder will retreive module and repository value automatically.\n";
	print "  If no local copy of repository are available or to force other values, use:\n";
	print "  -m=module           To force value of module name\n";
	print "  -d=repository       To force value of CVSROOT\n";
	print "\n";
	print "Options are:\n";
	print "  -branch=branchname  To work on another branch than default branch (!)\n";
	print "  -tagstart=tagname   To specify start tag version\n";
	print "  -tagend=tagend      To specify end tag version\n";
	print "\n";
	print "  WARNING: If you use tagstart and/or tagend, check that tags are in SAME\n";
	print "  BRANCH. Also, it must be the default branch, if not, you MUST use -branch to\n";
	print "  give the name of the branch, otherwise you will get unpredicable result.\n";
	print "\n";
	print "  -ssh                To run CVS through ssh (this only set CVS_RSH=\"ssh\")\n";
	print "  -debug=x            To get debug info with level x\n";
	print "  -rlogfile=rlogfile  To build changelog from an already existing rlog file\n";
	print "\n";
	print "Example:\n";
	print "  $PROG.$Extension -module=myproject -output=listdeltabyfile -tagstart=myproj_2_0 -d=john\@cvsserver:/cvsdir\n";
	print "  $PROG.$Extension -module=mymodule  -output=listdeltabydate -d=:ntserver:127.0.0.1:d:/mycvsdir\n";
	print "  $PROG.$Extension -module=mymodule  -output=listdeltabylog  -d=:pserver:user\@127.0.0.1:/usr/local/cvsroot\n";
	print "\n";
	exit 0;
}

# Get current time
my $nowtime=time;
my ($nowsec,$nowmin,$nowhour,$nowday,$nowmonth,$nowyear) = localtime($nowtime);
if ($nowyear < 100) { $nowyear+=2000; } else { $nowyear+=1900; }
my $nowsmallyear=$nowyear;$nowsmallyear =~ s/^..//;
if (++$nowmonth < 10) { $nowmonth = "0$nowmonth"; }
if ($nowday < 10) { $nowday = "0$nowday"; }
if ($nowhour < 10) { $nowhour = "0$nowhour"; }
if ($nowmin < 10) { $nowmin = "0$nowmin"; }
if ($nowsec < 10) { $nowsec = "0$nowsec"; }
# Get tomorrow time (will be used to discard some record with corrupted date (future date))
my ($tomorrowsec,$tomorrowmin,$tomorrowhour,$tomorrowday,$tomorrowmonth,$tomorrowyear) = localtime($nowtime+86400);
if ($tomorrowyear < 100) { $tomorrowyear+=2000; } else { $tomorrowyear+=1900; }
my $tomorrowsmallyear=$tomorrowyear;$tomorrowsmallyear =~ s/^..//;
if (++$tomorrowmonth < 10) { $tomorrowmonth = "0$tomorrowmonth"; }
if ($tomorrowday < 10) { $tomorrowday = "0$tomorrowday"; }
if ($tomorrowhour < 10) { $tomorrowhour = "0$tomorrowhour"; }
if ($tomorrowmin < 10) { $tomorrowmin = "0$tomorrowmin"; }
if ($tomorrowsec < 10) { $tomorrowsec = "0$tomorrowsec"; }
my $timetomorrow=$tomorrowyear.$tomorrowmonth.$tomorrowday.$tomorrowhour.$tomorrowmin.$tomorrowsec;	

# Check/Retreive module
if (! $Module) {
	if (-s "CVS/Repository") {
		open(REPOSITORY,"<CVS/Repository") || error("Failed to open 'CVS/Repository' file to get module name.");
		while (<REPOSITORY>) {
			chomp $_; s/\r$//;
			$Module=$_;
			last;
		}
		close(REPOSITORY);
	}
}
if (! $Module) {
	print "\n";
	error("The module name was not provided and could not be detected.\nUse -m=cvsmodulename option to specifiy module name.\n\nExample: $PROG.$Extension -output=$Output -module=mymodule -d=:pserver:user\@127.0.0.1:/usr/local/cvsroot");
}
print ucfirst($PROG)." launched for module: $Module\n";

# Check/Retreive CVSROOT environment variable (needed only if no option -rlogfile)
if (! $RLogFile) {
	if (! $CvsRoot) {
		# Try to set CvsRoot from CVS repository
		if (-s "CVS/Root") {
			open(REPOSITORY,"<CVS/Root") || error("Failed to open 'CVS/Root' file to get repository value.");
			while (<REPOSITORY>) {
				chomp $_; s/\r$//;
				$CvsRoot=$_;
				last;
			}
			close(REPOSITORY);
		}
	}
	if (! $CvsRoot) {
		# Try to set CvsRoot from CVSROOT environment variable
		if ($ENV{"CVSROOT"}) { $CvsRoot=$ENV{"CVSROOT"}; }
	}
	if (! $CvsRoot) {
		print "\n";
		error("The repository value to use was not provided and could not be detected.\nUse -d=repository option to specifiy repository value.\n\nExample: $PROG.$Extension -output=$Output -module=mymodule -d=:pserver:user\@127.0.0.1:/usr/local/cvsroot");
	}

	$ENV{"CVSROOT"}=$CvsRoot;
	print ucfirst($PROG)." launched for repository: $CvsRoot\n";

}


# Set use of ssh or not
if ($UseSsh) {
	print "Set CVS_RSH=ssh\n";
	$ENV{'CVS_RSH'}='ssh';
}

# SUMMARY OF PARAMETERS
#------------------------------------------

# LAUNCH CVS COMMAND RLOG TO WRITE RLOGFILE
#------------------------------------------
if (! $RLogFile) {
	# Define temporary file
	my $TmpDir="";
	$TmpDir||=$ENV{"TMP"};
	$TmpDir||=$ENV{"TEMP"};
	my $TmpFile="$TmpDir/$PROG.$$.tmp";
	open(TEMPFILE,">$TmpFile") || error("Failed to open temp file '$TmpFile' for writing. Check directory and permissions.");
	my $command;
	#$command="$CVSCLIENT rlog ".($TagStart||$TagEnd?"-r$TagStart:$TagEnd ":"")."$Module";
	if ($Branch) {
		$command="$CVSCLIENT -d ".$ENV{"CVSROOT"}." rlog -r${Branch} $Module";
	}
	else {
		$command="$CVSCLIENT -d ".$ENV{"CVSROOT"}." rlog".($TagStart||$TagEnd?" -r${TagStart}::${TagEnd}":"")." $Module";
	}
	print "Building temporary cvs rlog file '$TmpFile'\n";
	print "with command '$command'\n";
	debug("CVSROOT value is '".$ENV{"CVSROOT"}."'");
	my $result=`$command 2>&1`;
	print TEMPFILE "$result";
	close TEMPFILE;
	if ($result !~ /cvs \w+: Logging/i) {		# With log we get 'cvs server: Logging awstats' and with rlog we get 'cvs rlog: Logging awstats'
		error("Failure in cvs command: '$command'\n$result");
	}
	$RLogFile=$TmpFile;
}

# ANALYZE RLOGFILE
#------------------------
print("Formating output $Output from rlog file '$RLogFile'...\n\n");
debug("Formating output $Output from rlog file '$RLogFile'...");
open(RLOGFILE,"<$RLogFile") || error("Can't open rlog file");
my $waitfor="filename";
while (<RLOGFILE>) {
	chomp $_; s/\r$//;
	my $line="$_";

	debug("Analyze line $line (waitfor=$waitfor)",3);

	# Check if there is a warning in rlog file
	#if ($line =~ /^cvs rlog: warning: no revision/) { print("$line\n"); next; }

	# Wait for a new file
	if ($waitfor eq "filename") {
		if ($line =~ /$EXTRACTFILENAME/i) {
			$filename=$1;
			$filename =~ s/,v$//g;					# Clean filename if ended with ",v"
			# We found a new filename
			$waitfor="symbolic_name";
			debug("Found a new file '$filename'");
			#filename=ExcludeRepositoryFromPath($filename);
			$maxincludedver{"$filename"}=0;
			$minexcludedver{"$filename"}=0;
		}
		next;
	}

	# Wait for symbolic names area
	if ($waitfor eq "symbolic_name") {
		if ($line =~ /$EXTRACTSYMBOLICNAMEAREA/i) {
			# We found symbolic names area
			$waitfor="symbolic_name_entry";
			debug("Found symbolic name area");
		}
		next;
	}

	# Wait for symbolic names entry
	if ($waitfor eq "symbolic_name_entry") {
		if ($line =~ /$EXTRACTSYMBOLICNAMEENTRY/i) {
			# We found symbolic name entry
			# We set symbolic name. Example: $filesym{$filename}{MYAPPLI_1_0}=1.2
			$filesym{$filename}{$1}=$2;
			debug("Found symbolic name entry $1 is for version $filesym{$filename}{$1}");
			if ($TagEnd && $TagEnd eq $1) {
				$maxincludedver{"$filename"}=$2;
				debug(" Max included version for file '$filename' set to $2");
			}
			if ($TagStart && $TagStart eq $1) {
				$minexcludedver{"$filename"}=$2;
				debug(" Min excluded version for file '$filename' set to $2");
			}
		}
		else {
			$waitfor="revision";
		}
		next;
	}

	# Wait for a revision
	if ($waitfor eq "revision") {
		if ($line =~ /^=====/) {
			# No revision found
			$waitfor="filename";
			debug(" No revision found. Waiting for next $waitfor.");
			$filedate=''; $fileauthor=''; $filestate=''; $filechange=''; $filelog='';
			next;	
		}
		if ($line =~ /$EXTRACTFILEVERSION/i) {
			# We found a new revision number
			$fileversion=$1;
			$waitfor="dateauthorstate";
			debug("Found a new revision number $fileversion");
		}
		next;
	}

	# Wait for date and author of revision
	if ($waitfor eq "dateauthorstate") {
		if ($line =~ /$EXTRACTFILEDATEAUTHORSTATE/i) {
			# We found date/author line
			$filedate=$1; $fileauthor=$2; $filestate=$3; $filechange=$4;
			$filedate =~ s/[\s;]+$//; $fileauthor =~ s/[\s;]+$//; $filestate =~ s/[\s;]+$//; $filechange =~ s/\s+//g;
			$waitfor="log";
			debug("Found a new date/author/state $filedate $fileauthor $filestate");
		}
		next;
	}

	# Wait for log comment
	if ($waitfor eq "log") {
		if ($line =~ /^branches:/) { next; }
		if ($line =~ /^-----/) {
			$waitfor="revision";
			LoadDataInMemory();
			debug(" Revision info are stored. Waiting for next $waitfor.");
			$filedate=''; $fileauthor=''; $filestate=''; $filechange=''; $filelog='';
			next;	
		}
		if ($line =~ /^=====/) {
			$waitfor="filename";
			LoadDataInMemory();
			debug(" Revision info are stored. Waiting for next $waitfor.");
			$filedate=''; $fileauthor=''; $filestate=''; $filechange=''; $filelog='';
			next;	
		}
		# Line is log
		debug("Found a new line for log $line");
		$filelog.="$line\n";
		next;
	}
}

# BUILD OUTPUT
#------------------------
print "\nChanges for $Module";
if ($Branch) {
	print " in branch $Branch";	
}
if ($TagStart) {
	if ($TagEnd) { print " beetween $TagStart and $TagEnd"; }
	else { print " since $TagStart"; }
}
elsif ($TagEnd) {
	print " with $TagEnd";
}
print "\n built by $PROG $VERSION with option $Output.\n\n";


# For output by date
if ($Output =~ /bydate$/ || $Output =~ /forrpm$/) {
	if (scalar keys %DateAuthorChange) {
		foreach my $date (reverse sort keys %DateAuthorChange) {
			my $firstlineprinted=0;
			foreach my $logcomment (sort keys %{$DateAuthorLogChange{$date}}) {
				foreach my $revision (sort keys %{$DateAuthorLogFileRevChange{$date}{$logcomment}}) {
					$revision=~/(.*)\s([\d\.]+)/;
					my ($file,$version)=($1,$2);
					if ($maxincludedver{"$file"} && (CompareVersionBis($2,$maxincludedver{"$file"}) > 0)) { debug("For file '$file' $2 > maxincludedversion= ".$maxincludedver{"$file"},3); next; }
					if ($minexcludedver{"$file"} && (CompareVersionBis($2,$minexcludedver{"$file"}) <= 0)) { debug("For file '$file' $2 <= minexcludedversion= ".$minexcludedver{"$file"},3); next; }
					if (! $firstlineprinted) {
						if ($Output =~ /forrpm$/) { print "* ".FormatDate($date,'rpm')."\n"; }
						else { print FormatDate($date)."\n"; }
						$firstlineprinted=1;
					}
					my $state=$DateAuthorLogFileRevChange{$date}{$logcomment}{$revision};
					$state =~ s/_forced//;
					if ($Output !~ /forrpm$/) {
						print "\t* ".ExcludeRepositoryFromPath($file)." $version ($state):\n";
					}
				}
				chomp $logcomment;
				$logcomment =~ s/\r$//;
				if ($firstlineprinted) {
					foreach my $logline (split(/\n/,$logcomment)) {
						if ($Output =~ /forrpm$/) { print "\t- $logline\n"; }
						else { print "\t\t$logline\n"; }
					}
				}
			}
			if ($firstlineprinted) { print "\n"; }
		}	
	}
	else {
		print "No change detected.\n";	
	}
}

# For output by file
if ($Output =~ /byfile$/) {
	if (scalar keys %FilesLastVersion) {
		foreach my $file (sort keys %FilesLastVersion) {
			my $firstlineprinted=0;
			my $val='';
			foreach my $version (sort { &CompareVersion($a,$b) } keys %{$FilesChangeDate{$file}}) {
			#foreach my $revision (sort { ${$FilesChangeOrder{$file}{$b}} <=> ${$FilesChangeOrder{$file}{$a}} } keys ( %{$FilesChangeOrder{$file}} ) {
				if ($maxincludedver{"$file"} && (CompareVersionBis($version,$maxincludedver{"$file"}) > 0)) { debug("For file '$file' $version > maxincludedversion= ".$maxincludedver{"$file"},3); next; }
				if ($minexcludedver{"$file"} && (CompareVersionBis($version,$minexcludedver{"$file"}) <= 0)) { debug("For file '$file' $version <= minexcludedversion= ".$minexcludedver{"$file"},3); next; }
				if (! $firstlineprinted) {
					print ExcludeRepositoryFromPath($file)."\n";
					$firstlineprinted=1;
				}
				printf ("\t* %-16s ",$version." (".$FilesChangeState{$file}{$version}.")");
				print FormatDate($FilesChangeDate{$file}{$version})."\t$FilesChangeAuthor{$file}{$version}\n";
				my $logcomment=$FilesChangeLog{$file}{$version};
				chomp $logcomment;
				$logcomment =~ s/\r$//;
				if ($firstlineprinted) {
					foreach my $logline (split(/\n/,$logcomment)) {
						print "\t\t$logline\n";
					}
				}
			}
		}	
	}
	else {
		print "No change detected.\n";	
	}
}

# For output by log
if ($Output =~ /bylog$/) {
	if (scalar keys %LogChange) {
		foreach my $logcomment (sort keys %LogChange) {
			my $firstlineprinted=0;
			my $newlogcomment=substr($logcomment,0,$LGMAXLOG);
			if (length($logcomment)>$LGMAXLOG) { $newlogcomment.="..."; }
			foreach my $revision (sort { &CompareVersion($a,$b) } keys %{$LogChangeDate{$logcomment}}) {
				$revision=~/^(.*)\s([\d\.]+)$/;
				my ($file,$version)=($1,$2);
				if ($maxincludedver{"$file"} && (CompareVersionBis($2,$maxincludedver{"$file"}) > 0)) { debug("For file '$file' $2 > maxincludedversion= ".$maxincludedver{"$file"},3); next; }
				if ($minexcludedver{"$file"} && (CompareVersionBis($2,$minexcludedver{"$file"}) <= 0)) { debug("For file '$file' $2 <= minexcludedversion= ".$minexcludedver{"$file"},3); next; }
				if (! $firstlineprinted) {
					print "$newlogcomment\n";
					$firstlineprinted=1;
				}
				$file=ExcludeRepositoryFromPath($file);
				print "\t* ".FormatDate($LogChangeDate{$logcomment}{$revision})." $LogChangeAuthor{$logcomment}{$revision}\t $file $version ($LogChangeState{$logcomment}{$revision})\n";
			}
			if ($firstlineprinted) { print "\n"; }
		}	
	}
	else {
		print "No change detected.\n";	
	}
}

0;
