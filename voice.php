This is the article we've been trying to....<?php
if(empty($_GET['word'])) echo '<input type="button" value="Read All" onclick="Dom.speak()" data-read="#article">';
else{
	$word=$_GET['word'];
	echo $word.'<input type="button" value="Talk" onclick="Dom.speak()" data-text="'.$word.'">';
}